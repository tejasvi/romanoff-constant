"""Regenerate the 45a divisor-form certificates (format r45a-u3e) from cert_u3c_73.json (written by make_u3_certs.py):
cert_u3e_73.json (U3b's data, consistency), cert_u3d_37e.json (U3d), cert_u3e_23_37.json (U3e), cert_v4d_37e.json (V4d, conditional,
mu = 3.676e-3 norm rounded to 10^-12) and the four negative controls negctl_u3e_*.json.
Usage: make_u3de_certs.py DIR   (DIR contains cert_u3c_73.json; the outputs are written there)"""
import json, copy, math, sys, os
from fractions import Fraction as Fr

d = sys.argv[1]
c = json.load(open(os.path.join(d, 'cert_u3c_73.json')))
x = json.load(open(os.path.join(d, 'cert_u3c_73.json'))); x['format'] = 'r45a-u3e'; x['note'] = 'CONSISTENCY (divisor form): ' + x['note']
json.dump(x, open(os.path.join(d, 'cert_u3e_73.json'), 'w'), indent=1)

ordm = {3: 2, 5: 4, 7: 3, 11: 10, 13: 12, 17: 8, 31: 5, 241: 24, 41: 20, 19: 18, 73: 9, 37: 36, 23: 11}
def per_of(ords):
    P = 1
    for o in ords: P = P * o // math.gcd(P, o)
    return P
for name, add, note in [('cert_u3d_37e.json', [41, 19, 73, 37], 'U3d: BASE (period 120) + ADD [41, 19, 73, 37] (period 360; 37 last), divisor form.'),
                        ('cert_u3e_23_37.json', [41, 19, 73, 23, 37], 'U3e: BASE (period 120) + ADD [41, 19, 73, 23, 37] (period 3960; 37 last), divisor form.')]:
    x = copy.deepcopy(c); x['format'] = 'r45a-u3e'
    x['params']['ELL'] = [3, 5, 7, 11, 13, 17, 31, 241] + add
    x['ADD'] = add
    P = per_of([ordm[p] for p in x['params']['ELL']])
    x['PER'] = P; x['alpha_j'] = {str(P): '1'}; x['note'] = note
    json.dump(x, open(os.path.join(d, name), 'w'), indent=1)

c4 = json.load(open(os.path.join(d, 'cert_u3d_37e.json')))
ELL = c4['params']['ELL']; PER = c4['PER']
r = 1.0
for p in ELL: r *= p / (p - 1)
norm = r / (PER * math.log(2))
mu = Fr(round(3.676e-3 * norm * 1e12), 10**12)
x = copy.deepcopy(c4)
x['params']['C1'] = '67814/10000'
x['params']['note'] = 'CONDITIONAL on (I2) (Johnston-Trudgian Prop. 2 from Lichtman): budget constant C1 = 6.7814.'
x['mu'] = str(mu)
x['note'] = 'CONDITIONAL ' + c4['note'] + f' Uniform budget multiplier mu = {float(mu):.6e} (= 3.676e-3 norm).'
json.dump(x, open(os.path.join(d, 'cert_v4d_37e.json'), 'w'), indent=1)

ce = json.load(open(os.path.join(d, 'cert_u3e_73.json')))
def mk(name, mod, note):
    x = copy.deepcopy(ce); mod(x); x['note'] = note
    json.dump(x, open(os.path.join(d, name), 'w'), indent=1)
mk('negctl_u3e_alpha_mass.json', lambda x: x.update(alpha_j={'360': '1001/1000'}), 'NEGATIVE CONTROL (u3e): alpha_j mass 1.001 R0tail; must FAIL.')
mk('negctl_u3e_wrong_vertex.json', lambda x: x.update(alpha_j={'1': '1'}), 'NEGATIVE CONTROL (u3e): j at alpha = R0tail e_1, claim 0.110173 (the e_1 vertex value); must FAIL.')
def addnot(x): x['ADD'] = [41, 19, 73, 37]
mk('negctl_u3e_add_not_in_ell.json', addnot, 'NEGATIVE CONTROL (u3e): ADD contains 37, which is not in ELL; must FAIL.')
mk('negctl_u3e_orbits.json', lambda x: x.update(n_base_orbits=7871), 'NEGATIVE CONTROL (u3e): wrong base-orbit count; must FAIL.')
print('wrote cert_u3e_73, cert_u3d_37e, cert_u3e_23_37, cert_v4d_37e and 4 negctl_u3e certificates')
