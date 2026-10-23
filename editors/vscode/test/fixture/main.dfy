include "lib.dfy"
module App {
  import opened Lib
  method Abs(x: int) returns (y: int)
    ensures y >= 0
  {
    if x < 0 { y := -x; } else { y := x; }
  }
  lemma Bad(x: int)
    ensures x > 0
  {
  }
  method Use(s: Shape) {
    var a := Abs(3);
    var t := Twice(a);
    assert t == 2 * a;
  }
}
