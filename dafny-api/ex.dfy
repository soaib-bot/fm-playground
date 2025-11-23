method Abs(x: int) returns (y: int)
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}

method Swap(a: int, b: int) returns (x: int, y: int)
  ensures x == b && y == a
{
  x := b;
  y := a;
}