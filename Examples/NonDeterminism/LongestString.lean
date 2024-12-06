
-- Example of nondeterminism:
-- correct:      `longest("foo", "bar") = "foo"`
-- also correct: `longest("foo", "bar") = "bar"`

procedure longest(s1: string, s2: string) returns string {
  goto A, B;
A:
  assume |s1| <= |s2|
  return s2;
B:
  assume |s1| >= |s2|
  return s1;
}
