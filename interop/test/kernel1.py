#from nki import baremetal # breaks klr
import nki.isa as nisa
import nki.language as nl
import numpy as np
import klr

# test kernel 1 : t - 1.0 with no access pattern
# @nki.baremetal(artifacts_dir='kernel1-nki')
def kernel1(a):
  a_tile = nl.load(a)
  b_tile = nisa.tensor_scalar(a_tile, np.subtract, 1.0)
  b = nl.ndarray(b_tile.shape, dtype=b_tile.dtype, buffer=nl.shared_hbm)
  nl.store(b, b_tile)
  return b

def doit():
  a = np.zeros([10, 10], dtype=np.float32)
  c = kernel1(a)
  print(c)
  assert np.allclose(c, a - 1)

if __name__ == '__main__':
  F = klr.parser.Parser(kernel1)
  print(F.json())
