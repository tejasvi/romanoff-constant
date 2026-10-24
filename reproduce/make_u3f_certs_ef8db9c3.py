"""Write the r45a-u3f certificates from cert_u3e_23_37.json (make_u3de_certs.py output):
  cert_u3f_repro.json : U3e's data (period 3960) with 11 as an independent component (validation: must reproduce U3e);
  cert_u3g_27720.json : U3e's data + 43, 29 (period 27720; independent components 7 and 11).
Usage: make_u3f_certs.py DIR   (DIR contains cert_u3e_23_37.json)"""
import json, copy, os, sys

d = sys.argv[1]
c = json.load(open(os.path.join(d, 'cert_u3e_23_37.json')))
x = copy.deepcopy(c); x['format'] = 'r45a-u3f'; x['IND'] = [11]
x['note'] = 'VALIDATION: U3e data (period 3960) with 11 as an independent CRT component; must reproduce U3e.'
json.dump(x, open(os.path.join(d, 'cert_u3f_repro.json'), 'w'), indent=1)
y = copy.deepcopy(c); y['format'] = 'r45a-u3f'
y['params']['ELL'] = y['params']['ELL'] + [43, 29]; y['ADD'] = y['ADD'] + [43, 29]; y['IND'] = [7, 11]
y['PER'] = 27720; y['alpha_j'] = {'27720': '1'}
y['note'] = 'U3g: BASE (period 120) + core ADD [41, 19, 73, 37] (period 360) + independent 7: [43, 29], 11: [23] (period 27720).'
json.dump(y, open(os.path.join(d, 'cert_u3g_27720.json'), 'w'), indent=1)
print('wrote cert_u3f_repro.json, cert_u3g_27720.json')
