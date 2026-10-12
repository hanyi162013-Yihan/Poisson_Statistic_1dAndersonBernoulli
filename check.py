#!/usr/bin/env python3
"""Reproducible local build and complete public-theorem axiom audit.
Run with `python3 check.py` from any directory. Requires the pinned Lean toolchain
and public dependencies (Lake fetches these; mathlib's cache may be fetched first).
No checking limits are changed. Nonzero subprocess statuses are always propagated.
"""
from pathlib import Path
import subprocess, re, json, hashlib, sys

ROOT = Path(__file__).resolve().parent
LOG = ROOT / 'check.log'
AUDIT_LOG = ROOT / 'axiom_audit.log'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def code_only(src):
    """Erase nested Lean comments and strings, preserving newlines for auditing."""
    out=[]; i=0; depth=0; string=False
    while i < len(src):
        if depth:
            if src[i:i+2]=='/-': depth+=1; i+=2
            elif src[i:i+2]=='-/': depth-=1; i+=2
            else:
                out.append('\n' if src[i]=='\n' else ' '); i+=1
        elif string:
            if src[i]=='\\': out.extend('  '); i+=2
            elif src[i]=='"': string=False; out.append(' '); i+=1
            else: out.append('\n' if src[i]=='\n' else ' '); i+=1
        elif src[i:i+2]=='/-': depth=1; i+=2
        elif src[i:i+2]=='--':
            end=src.find('\n',i); end=len(src) if end<0 else end
            out.extend(' '*(end-i)); i=end
        elif src[i]=='"': string=True; out.append(' '); i+=1
        else: out.append(src[i]); i+=1
    if depth or string: raise RuntimeError('Unterminated comment or string')
    return ''.join(out)


def run(args, log):
    print('Checking:', ' '.join(args), flush=True)
    result = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    with log.open('a') as f: f.write(result.stdout)
    if result.stdout: print(result.stdout, end='', flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
    return result.stdout


def public_theorems(path):
    src=code_only(path.read_text())
    if re.search(r'\b(sorry|admit|sorryAx)\b', src):
        raise RuntimeError(f'Forbidden placeholder in {path.name}')
    if re.search(r'^\s*(?:unsafe\s+)?(?:axiom|opaque)\s',src,re.M):
        raise RuntimeError(f'Unproved axiom/opaque declaration in {path.name}')
    if re.search(r'\bset_option\s+(?:maxHeartbeats|maxRecDepth|maxSynthPendingDepth|.*[Tt]imeout)\b',src):
        raise RuntimeError(f'Checking limit override in {path.name}')
    stack=[]; result=[]
    for line in src.splitlines():
        ns=re.match(r'\s*namespace\s+(\S+)',line)
        if ns: stack.append(ns.group(1)); continue
        end=re.match(r'\s*end\s+(\S+)',line)
        if end and stack and end.group(1)==stack[-1]: stack.pop(); continue
        if re.search(r'\bprivate\s+(?:theorem|lemma)\b',line): continue
        m=re.search(r'\b(?:theorem|lemma)\s+([A-Za-z_][\w.\'₀-₉]*)',line)
        if m: result.append('.'.join(stack+[m.group(1)]))
    return result


def main():
    from main_status_guard import INPUT_CONSTRUCTION, main_status
    LOG.write_text('')
    AUDIT_LOG.write_text('')
    for name in ('check_result.json', 'checked_theorems.json'):
        (ROOT/name).unlink(missing_ok=True)
    sources=sorted((ROOT/'FixedCouplingPoisson').glob('*.lean'))
    inputs=sources+[ROOT/name for name in ('FixedCouplingPoisson.lean',
        'lakefile.toml','lean-toolchain','lake-manifest.json','check.py','main_status_guard.py')]
    hashes={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in inputs}
    theorems=[(p, name) for p in sources for name in public_theorems(p)]
    if len({name for _,name in theorems}) != len(theorems):
        raise RuntimeError('Duplicate public theorem names in source inventory')
    run(['lake','build'],LOG)
    constructions = ([INPUT_CONSTRUCTION] if
        ROOT/'FixedCouplingPoisson/FurstenbergInputProved.lean' in sources else [])
    expected_names = {name for _,name in theorems} | set(constructions)
    audit=ROOT/'AxiomAudit.lean'
    audit.write_text('import FixedCouplingPoisson\n\n'+''.join(
        f'#print axioms {name}\n' for name in
        [name for _,name in theorems] + constructions))
    output=run(['lake','env','lean',str(audit)],AUDIT_LOG)
    if 'sorryAx' in output: raise RuntimeError('sorryAx found by transitive audit')
    # Lean wraps some axiom lists onto several lines. Match the whole bracketed
    # list rather than silently dropping dependencies on continuation lines.
    closures=re.findall(r"^'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]",output,re.M)
    free=re.findall(r"^'([^\n]+)' does not depend on any axioms",output,re.M)
    names=[name for name,_ in closures]+free
    for name,raw in closures:
        axioms={x.strip() for x in raw.split(',') if x.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise RuntimeError(f'Unexpected transitive axioms for {name}: {axioms-ALLOWED_AXIOMS}')
    seen=len(names)
    if seen != len(expected_names) or set(names) != expected_names:
        raise RuntimeError(f'Axiom audit inventory mismatch: {seen} outputs, expected {len(expected_names)} named declarations')
    if any(hashlib.sha256(p.read_bytes()).hexdigest() != hashes[str(p.relative_to(ROOT))]
           for p in inputs):
        raise RuntimeError('A source or dependency declaration changed during checking; rerun')
    records=[{'file':str(p.relative_to(ROOT)), 'theorem':name} for p,name in theorems]
    (ROOT/'checked_theorems.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
    main_evidence = main_status(ROOT, hashes, names, code_only,
        complete_build=True, complete_axiom_audit=True)
    main_proved = main_evidence['main_poisson_theorem'] != 'NOT PROVED'
    report={'status':('checked_main_formalization' if main_proved else 'checked_partial_formalization'),
            'public_theorems_audited':len(theorems),
            'named_constructions_audited':constructions,
            'allowed_foundational_axioms':sorted(ALLOWED_AXIOMS),
            'source_sha256':hashes, **main_evidence}
    (ROOT/'check_result.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(f"PASS: complete build; {len(theorems)} public theorem closures and "
          f"{len(constructions)} named constructions audited. "
          f"Main Poisson theorem: {main_evidence['main_poisson_theorem']}.")

if __name__=='__main__':
    try: main()
    except RuntimeError as err:
        print('CHECK FAILED:',err,file=sys.stderr); raise SystemExit(1)
