# Declares variables: var

```
var nish: int;
var m := 5;	/* inferred type */
var i: int, j: nat;
var x, y, z: bool := 1, 2, true;
```

# Assignment: :=

```
z := false;
x, y := x+y, x-y;	/* parallel assignment */
```

# Conditional statement: if..else

```
if z { x := x + 1; }	/* braces are */
else { y := y - 1; }	/* mandatory */
```

# Conditional expression: if..then ..else

```
m := if x < y then x else y;
```

# Loops: while forall

```
while x > y { x := x - y; }
forall i | 0 <= i < m { Foo(i); }
```

# Subroutines: method returns

```
/* Without a return value */
method Hello() { print “Hello Dafny”; }
/* With a return value */
method Norm2(x: real, y: real)
  returns (z: real)	/* return values */
{	/* must be named */
  z := x * x + y * y;
}
/* Multiple return values */
method Prod(x: int) returns (dbl: int, trpl: int)
{ dbl, trpl := x * 2, x * 3; }
```

# Object classes: class

```
class Point	/* classes contain */
{	/* variables and methods */
  var x: real, y: real
  method Dist2(that: Point) returns (z: real)
    requires that != null
  { z := Norm2(x - that.x, y - that.y); }
}
```

# Typed arrays: array

```
var a := new bool[2];
a[0], a[1] := true, false;
method Find(a: array<int>, v: int)
  returns (index: int)
```

# Precondition: requires

```
method Rot90(p: Point) returns (q: Point)
  requires p != null
{ q := new Point; q.x, q.y := -p.y, p.x; }
```

# Postcondition: ensures

```
method max(a: nat, b: nat) returns (m: nat)
  ensures m >= a	/* can have as many */
  ensures m >= b	/* as you like */
{ if a > b { m := a; } else { m := b; } }
```

# Inline propositions: assert assume

```
assume x > 1;
assert 2 * x + x / x > 3;
```

# Logical connectives: ! && || ==> <== <==>

```
assume (z || !z) && x > y;
assert j < a.Length ==> a[j]*a[j] >= 0;
assert !(a && b) <==> !a || !b;
```

# Logical quantifiers: forall exists

```
assume forall n: nat :: n >= 0;
assert forall k :: k + 1 > k;	/* inferred k:int */
```

# Pure definitions: Function predicate


```
function min(a: nat, b: nat): nat
{	/* body must be an expression */
  if a < b then a else b
}
predicate win(a: array<int>, j: int)
  requires a != null
{	/* just like function(...): bool */
  0 <= j < a.Length
}
```

# Framing (for methods): modifies

```
method Reverse(a: array<int>)	/* not allowed to */
  modifies a	/* assign to elements of “a” otherwise */
```

# Framing (for functions): reads

```
predicate Sorted(a: array<int>)	/* not allowed to */
  reads a	/* refer to “a[_]” otherwise */
```

# Loop invariants: invariant

```
i := 0;
while i < a.Length
  invariant 0 <= i <= a.Length
  invariant forall k :: 0 <= k < i ==> a[k] == 0
{  a[i], i := 0, i + 1;  }
assert forall k :: 0 <= k < a.Length ==> a[k] == 0;
```

# Standard data types: set seq multiset

```
var s: set<int> := {4, 2};
assert 2 in s && 3 !in s;
var q: seq<int> := [1, 4, 9, 16, 25];
assert q[2] + q[3] == q[4];
assert forall k :: k in s ==> k*k in q[1..];
var t: multiset<bool> := multiset{true, true};
assert t - multiset{true} != multiset{};
/* more at: */
/* http://rise4fun.com/Dafny/tutorial/Collections */
```
