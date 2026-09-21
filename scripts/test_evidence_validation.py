"""Bounded negative tests for evidence validation; no mathematical verification."""
import copy
import json
import shutil
import subprocess
import tempfile
from pathlib import Path

root = Path(__file__).resolve().parents[1]
with tempfile.TemporaryDirectory(prefix='newton-evidence-') as tmp:
    work = Path(tmp)
    for folder in ['scripts','research','docs','NewtonLimitDynamics']:
        shutil.copytree(root/folder,work/folder,ignore=shutil.ignore_patterns('__pycache__'))
    dep_path = work/'research/dependencies.json'
    passage_path = work/'research/passages.json'
    original = json.loads(dep_path.read_text())
    passages = json.loads(passage_path.read_text())
    def check(success, expected=''):
        result=subprocess.run(['python3','scripts/check_graph.py'],cwd=work,capture_output=True,text=True)
        assert (result.returncode==0)==success, result.stdout+result.stderr
        if expected:
            assert expected in result.stderr, result.stderr
    check(True)
    bad=copy.deepcopy(original)
    bad['edges'][0]['url']='https://example.invalid/wrong'
    dep_path.write_text(json.dumps(bad))
    check(False,'stale edge url')
    bad=copy.deepcopy(original)
    edge=next(e for e in bad['edges'] if e['from']=='P1687.L9')
    edge['to']='P1713.L10'
    dep_path.write_text(json.dumps(bad))
    check(False,'AssertionError')
    bad=copy.deepcopy(original)
    edge=copy.deepcopy(next(e for e in bad['edges'] if e['from']=='P1687.L9'))
    edge['from'],edge['to']=edge['to'],edge['from']
    bad['edges'].append(edge)
    dep_path.write_text(json.dumps(bad))
    check(False,'cycle at')
    dep_path.write_text(json.dumps(original))
    bad=copy.deepcopy(passages)
    bad[0]['anchor']='missing_anchor'
    passage_path.write_text(json.dumps(bad))
    check(False,'AssertionError')
print('Passed baseline and four negative evidence-validation cases')
