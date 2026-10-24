"""Regenerate the 45a U3a / U3b certificate files (cert_u3a, cert_u3x_41, cert_u3b_19, cert_u3c_73) from U2's certificate.
The certificates carry no computed data: parameters, the added primes, the period, the BASE orbit count (recomputed and checked
by the checker) and the point alpha_j = R0tail e_PER at which the Pintz indices are chosen (the float model scan45c.py put the
minimum of the alpha-form bound at this vertex; any choice is valid).  Usage: make_u3_certs.py U2_CERT.json OUTDIR"""
import json, sys, os

u2, out = sys.argv[1], sys.argv[2]
base = json.load(open(u2))
par = dict(base['params'])
par['note'] = 'UNCONDITIONAL: (I2) unused; budget rows dropped; C1 = CAP does not enter the bound.'
u3a = {'format': 'r45a-u3', 'tail_mode': 'alpha_simplex', 'params': par, 'PER': 120, 'n_orbits': 92206,
       'alpha_j': {'120': '1'},
       'note': 'U3a: ELL and data of U2 (period 120), adversarial class-(c) tail on the simplex; j at alpha = R0tail e_120.'}
json.dump(u3a, open(os.path.join(out, 'cert_u3a.json'), 'w'), indent=1)

def mk(ell, add, per, nb, note):
    c = dict(u3a); c['format'] = 'r45a-u3x'; c['params'] = dict(u3a['params']); c['params']['ELL'] = ell
    c['ADD'] = add; c['PER'] = per; c.pop('n_orbits'); c['n_base_orbits'] = nb; c['alpha_j'] = {str(per): '1'}; c['note'] = note
    return c

v2 = [3, 5, 7, 11, 13, 17, 31, 241]
json.dump(mk(v2 + [41], [41], 120, 7870, 'CONSISTENCY: U3a recomputed as BASE (period 120, 7870 orbits) + ADD [41] option sums.'),
          open(os.path.join(out, 'cert_u3x_41.json'), 'w'), indent=1)
b19 = mk(v2 + [41, 19], [41, 19], 360, 7870, 'U3b: BASE (period 120) + ADD [41, 19] (period 360), adversarial class-(c) tail.')
json.dump(b19, open(os.path.join(out, 'cert_u3b_19.json'), 'w'), indent=1)
c73 = dict(b19); c73['params'] = dict(b19['params']); c73['params']['ELL'] = c73['params']['ELL'] + [73]; c73['ADD'] = [41, 19, 73]
c73['note'] = 'U3c: BASE (period 120) + ADD [41, 19, 73] (period 360), adversarial class-(c) tail.'
json.dump(c73, open(os.path.join(out, 'cert_u3c_73.json'), 'w'), indent=1)
print('wrote cert_u3a.json, cert_u3x_41.json, cert_u3b_19.json, cert_u3c_73.json')
