"""Write three test certificates for the divisor-form checker (format r45a-u3e) from cert_u3x_41 (the split test of the
modulus 3*5*7*11*13*17*31*41*241): cert_u3e_41.json (the same certificate in format r45a-u3e, 41 as the last added
prime), and cert_u3e_41_23.json and cert_u3e_23_41.json (the added primes 41 and 23, period 1320, with 23 or 41 as the
last added prime).  Usage: make_u3e_tests.py CERT_U3X_41.json OUTDIR"""
import copy, json, os, sys

c = json.load(open(sys.argv[1])); d = sys.argv[2]
BASE = [3, 5, 7, 11, 13, 17, 31, 241]
x = copy.deepcopy(c); x['format'] = 'r45a-u3e'
x['note'] = 'TEST: cert_u3x_41 in format r45a-u3e (41 is the last added prime).'
json.dump(x, open(os.path.join(d, 'cert_u3e_41.json'), 'w'), indent=1)
for add, name in (([41, 23], 'cert_u3e_41_23.json'), ([23, 41], 'cert_u3e_23_41.json')):
    y = copy.deepcopy(x)
    y['params']['ELL'] = BASE + add; y['ADD'] = add; y['PER'] = 1320; y['alpha_j'] = {'1320': '1'}
    y['note'] = f'TEST: period 1320, added primes {add[0]} and {add[1]} ({add[1]} is the last added prime).'
    json.dump(y, open(os.path.join(d, name), 'w'), indent=1)
print('wrote cert_u3e_41, cert_u3e_41_23, cert_u3e_23_41')
