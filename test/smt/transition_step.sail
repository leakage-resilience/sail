default Order dec

$include <flow.sail>
$include <arith.sail>
$include <vector_dec.sail>

register R1 : bits(16)
register R2 : bits(8)

function step(x : bits(16)) -> bool = {
  R1 = x;
  R2 = 0x00;
  true
}
