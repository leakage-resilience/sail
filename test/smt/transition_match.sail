default Order dec

$include <prelude.sail>

register R1 : bits(2)

function step(idx : bits(2)) -> unit = {
  R1 = match idx {
    0b00 => 0b01,
    0b01 => 0b10
  }
}
