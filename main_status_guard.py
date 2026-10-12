"""Final-report guard; does not run Lean or edit any project file.

The caller must supply evidence only after the real complete build and the
complete parsed axiom audit succeed. Archive/finish must additionally verify
the real full-check terminal receipt and unchanged frozen policy hashes.
"""
from pathlib import Path
import hashlib
import re

CONDITIONAL_THEOREMS = tuple('FixedCouplingPoisson.' + name for name in (
    'idsSpectralVagueLaw_tendsto_poissonVagueLaw',
    'linearSpectralVagueLaw_tendsto_poissonVagueLaw',
    'idsSpectralCountingLaw_tendsto_poissonCountingLaw',
    'linearSpectralCountingLaw_tendsto_poissonCountingLaw',
    'bernoulli_idsSpectralCountingLaw_tendsto_poissonCountingLaw',
))
UNCONDITIONAL_THEOREMS = tuple(name + '_of_potentialLaw' for name in CONDITIONAL_THEOREMS)
INPUT_CONSTRUCTION = 'FixedCouplingPoisson.Furstenberg.provedFurstenbergInput'

# These fingerprints bind the approved exact type ascriptions, allowing only
# whitespace/comment changes. They are not hashes of theorem names alone.
GUARD_CODE_SHA256 = {
    'SpectralPoissonStatementTypes': '4d2528d897c20329fea4a1a397808eed549e438bf49697e65e0768901b1923c9',
    'SpectralPoissonUnconditionalStatementTypes': 'df65147ed4204270182e6fda51d44dac51e29f4d1fc11ab4837f431158bbdad5',
}


def main_status(project, source_sha256, audited_names, code_only, *,
                complete_build=False, complete_axiom_audit=False):
    """Classify only actual, fully audited, exactly guarded main statements."""
    project = Path(project)
    names = set(audited_names)
    reasons = []
    if not complete_build or not complete_axiom_audit:
        return {'main_poisson_theorem': 'NOT PROVED',
                'main_statement_evidence': [],
                'main_status_missing': ['Actual complete build and axiom audit required.']}
    root_code = code_only((project / 'FixedCouplingPoisson.lean').read_text())
    imports = set(re.findall(r'^\s*import\s+(\S+)\s*$', root_code, re.M))

    def frozen_module(name):
        path = project / 'FixedCouplingPoisson' / (name + '.lean')
        key = path.relative_to(project).as_posix()
        return (path.is_file() and key in source_sha256 and
                hashlib.sha256(path.read_bytes()).hexdigest() == source_sha256[key] and
                'FixedCouplingPoisson.' + name in imports)

    def guarded(name):
        if not frozen_module(name):
            return False
        text = (project / 'FixedCouplingPoisson' / (name + '.lean')).read_text()
        normalized = ''.join(code_only(text).split())
        return hashlib.sha256(normalized.encode()).hexdigest() == GUARD_CODE_SHA256[name]

    conditional = (set(CONDITIONAL_THEOREMS) <= names and
                   frozen_module('SpectralPoissonLimit') and
                   guarded('SpectralPoissonStatementTypes'))
    unconditional = (conditional and set(UNCONDITIONAL_THEOREMS) <= names and
                     INPUT_CONSTRUCTION in names and
                     frozen_module('FurstenbergInputProved') and
                     frozen_module('SpectralPoissonUnconditional') and
                     guarded('SpectralPoissonUnconditionalStatementTypes'))
    if unconditional:
        status = 'PROVED_FOR_POTENTIAL_LAW'
        evidence = list(CONDITIONAL_THEOREMS + UNCONDITIONAL_THEOREMS) + [INPUT_CONSTRUCTION]
    elif conditional:
        status = 'PROVED_WITH_EXPLICIT_FURSTENBERG_INPUT'
        evidence = list(CONDITIONAL_THEOREMS)
        reasons.append('Unconditional wrappers/construction/second exact type guard not all audited.')
    else:
        status = 'NOT PROVED'
        evidence = []
        reasons.append('Five conditional main statements and approved exact type guard not all audited.')
    return {'main_poisson_theorem': status,
            'main_statement_evidence': evidence,
            'main_status_missing': reasons}
