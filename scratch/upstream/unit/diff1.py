import json, sys, difflib
b = {json.loads(l)['id']: json.loads(l) for l in open(sys.argv[1])}
j = {json.loads(l)['id']: json.loads(l) for l in open(sys.argv[2])}
ids = sys.argv[3:] or [l.split()[1] for l in sys.stdin if l.startswith('wrong')]
for i in ids:
    r, t = b[i], j[i]
    print('=====', i, 'exit', r['exit'], 'jar', t['exit'])
    d = [x for x in difflib.unified_diff(t['transcript'].split('\n'), r['transcript'].split('\n'), 'jar', 'prove-it', n=0, lineterm='') if not x.startswith(('---','+++','@@'))]
    print('\n'.join(d[:8]))
