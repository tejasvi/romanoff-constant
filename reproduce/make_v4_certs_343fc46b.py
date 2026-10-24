"""Regenerate the 45a conditional certificates cert_v4a_41.json and cert_v4b{a,b,c}_73.json from cert_u3x_41.json and
cert_u3c_73.json (written by make_u3_certs.py).  The only new data are C1 = 6.7814 and the uniform budget multiplier mu:
  V4a: mu = 13022/10^8, the optimum of the float model scan45e.py at period 120 (absolute grid);
  V4b: mu = t * norm rounded to 10^-10, t = 3.660e-3, 3.676e-3, 3.692e-3 around the optimum mu/norm ~ 3.676e-3 that scan45e.py
       found at periods 120 and 360; norm = (prod p/(p-1)) / (360 log 2) in floating point.  The exact checker runs of the three
       V4b certificates then picked t = 3.676e-3 (0.118601142 against 0.118593974 and 0.118598764).
Usage: make_v4_certs.py DIR   (DIR contains cert_u3x_41.json and cert_u3c_73.json; the outputs are written there)"""
import json, copy, math, sys, os
from fractions import Fraction as Fr

d = sys.argv[1]
cond_note = 'CONDITIONAL on (I2) (Johnston-Trudgian Prop. 2 from Lichtman): budget constant C1 = 6.7814.'
c = json.load(open(os.path.join(d, 'cert_u3x_41.json')))
x = copy.deepcopy(c)
x['params']['C1'] = '67814/10000'
x['params']['note'] = cond_note
x['mu'] = '13022/100000000'
x['note'] = 'V4a (conditional): data of v3 (period 120, ELL incl. 41) as BASE + ADD [41]; uniform budget multiplier mu; adversarial class-(c) tail.'
json.dump(x, open(os.path.join(d, 'cert_v4a_41.json'), 'w'), indent=1)

ELL = [3, 5, 7, 11, 13, 17, 31, 241, 41, 19, 73]
r = 1.0
for p in ELL: r *= p / (p - 1)
norm = r / (360 * math.log(2))
c = json.load(open(os.path.join(d, 'cert_u3c_73.json')))
for tag, t in [('a', 3.660e-3), ('b', 3.676e-3), ('c', 3.692e-3)]:
    mu = Fr(round(t * norm * 1e10), 10**10)
    x = copy.deepcopy(c)
    x['params']['C1'] = '67814/10000'
    x['params']['note'] = cond_note
    x['mu'] = str(mu)
    x['note'] = f'V4b{tag} (conditional): BASE (period 120) + ADD [41, 19, 73] (period 360); uniform budget multiplier mu = {float(mu):.6e} (= {t} norm); adversarial class-(c) tail.'
    json.dump(x, open(os.path.join(d, f'cert_v4b{tag}_73.json'), 'w'), indent=1)
print('wrote cert_v4a_41.json, cert_v4ba_73.json, cert_v4bb_73.json, cert_v4bc_73.json')
