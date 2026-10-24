"""Write cert_v4g_27720.json (V4g: conditional on (I2); the U3g data, period 27720) from cert_u3g_27720.json (make_u3f_certs.py),
with the V4d/V4e rule: C1 = 6.7814, mu = 3.676e-3 norm rounded to 10^-12, norm = (prod p/(p-1)) / (PER log 2) in floating point.
Usage: make_v4g_cert.py DIR   (DIR contains cert_u3g_27720.json)"""
import json, copy, math, sys, os
from fractions import Fraction as Fr

d = sys.argv[1]
c = json.load(open(os.path.join(d, 'cert_u3g_27720.json')))
ELL = c['params']['ELL']; PER = c['PER']
r = 1.0
for p in ELL: r *= p / (p - 1)
norm = r / (PER * math.log(2))
mu = Fr(round(3.676e-3 * norm * 1e12), 10**12)
x = copy.deepcopy(c)
x['params']['C1'] = '67814/10000'
x['params']['note'] = 'CONDITIONAL on (I2) (Johnston-Trudgian Prop. 2 from Lichtman): budget constant C1 = 6.7814.'
x['mu'] = str(mu)
x['note'] = 'CONDITIONAL ' + c['note'] + f' Uniform budget multiplier mu = {float(mu):.6e} (= 3.676e-3 norm).'
json.dump(x, open(os.path.join(d, 'cert_v4g_27720.json'), 'w'), indent=1)
print('wrote cert_v4g_27720.json; mu =', mu)
