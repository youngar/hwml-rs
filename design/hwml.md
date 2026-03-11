The New, Terrible Idea
Core Language
Universes
HType: hardware types
MType: module types
SType: signal types
Type:  meta-level types

G |-
================= stype
G |- SType : Type

G |-
================= mtype
G |- MType : Type

G |-
================= htype
G |- HType : Type

G |- s : SType
================== htype/sig
G |- Sig s : HType

G |- m : MType
================== htype/mod
G |- Mod m : HType

G |-
================= type
G |- Type: Type+

G |- h : HType
============== type/lift
G |- ^h : Type
Modules and Functions
Modules
G |- a : SType
G |- b : HType
=================== mod/form
G |- a ~> b : MType

G |- a : SType
G |- b : HType
G, x : ^(Sig a) |- body : ^b
=============================== mod/intro
mod x => body : ^(Mod (a ~> b))

G |- a : SType
G |- b : HType
G |- f : ^(Mod (a -> b))
G |- x : ^(Sig a)
======================== mod/elim
G |- m x : ^b
Functions
G |- a : Type
G, x : a |- b : Type
==================== fun/form
(x : a) -> b : Type

G |- a : Type
G, x : a |- b : Type
G, x : a |- body : b
============================ fun/intro
G |- fun x => t : (x : A) => B

G |- a : Type
G, x : a |- b : Type
G |- f : (x : a) => b
G |- y : a
===================== fun/elim
G |- f y : b[y/x]
Let and Meta-Let
G |- h1 : HType
G |- h2 : HType
G |- y : ^h1
G, x : ^h1 |- z : ^h2
===================== let
let x := y in z : ^h2

G |- a : Type
G |- b : Type
G |- y : a
G, x : a |- z : b
======================== meta-let
meta let x := y in z : b
Data Types (TODO)
Record Types (TODO)
Examples
def foo : Bit -> Bit -> Bit :=
 mod x y => add x y

def bar : Bit -> Bit -> Bit :=
  mod x y := foo (foo x y) (foo x y)

module bar(
  input x : Bit
  input y : Bit
  output o : Bit
)
  wire out, out2;
  foo foo(x, y, out)
  foo foo2(x, y, out2)
  foo foo3(out, out2, o)
endmodule


def foo : Bit -> Bit -> Bit :=
 mod x y => add x y

def bar : Bit -> Bit -> Bit :=
  mod x y := foo (foo x y) (foo x y)

module bar(
  input x : Bit
  input y : Bit
  output o : Bit
)
  wire out, out2;
  foo foo(x, y, out)
  foo foo2(x, y, out2)
  foo foo3(out, out2, o)
endmodule

// Returns quoted hardware
def foo : Nat => Bit :=
 fun x => 0

// Error: module can't take a Nat?
def foo : Nat -> Bit :=
  mod x => 0

// Fine, can't really use the quoted hardware
def foo : Bit => Nat :=
 fun x => zero

// Error: module can't return a Nat?
def foo : Bit => Nat :=
  mod x => zero

// quoted argument, quoted result
def foo : Bit => Bit :=
 fun x => x

// regular module
def foo : Bit -> Bit :=
 mod x -> x

// Quoted arg, returns module
def foo : Bit => Bit -> Bit :=
  fun x => mod y -> x + y

// Regular module, return quoted module?
def foo : Bit -> Bit => Bit :=
  mod x -> fun y => x + y
// Does this one make sense??

Surface Language
At the surface, we have the following hardware universes:
  VType  – hardware value types (eg Bit)
  MType  – hardware module types (eg Bit -> Bit)
  Type   – any hardware type (eg Bit, or Bit -> Bit)
Examples:
Due to sub-kinding, hardware value types and module types belongs to multiple universes:

Bit : VType
Bit : Type
Bit : Kind
Bit -> Bit : MType
Bit -> Bit : Type
Bit -> Bit : Kind


0 ====> '0 : ^(Val Bit)
mod x => x + 1 : Bit -> Bit : Kind
Sub-Kinding (Surface)
The sub-kinding relationships are:
  VType << Type  – every value type is also a hardware level type.
  MType << Type  – every module type is also a hardware level type.
  Type  << Kind  – every hardware level type is also a kind.

The subtyping relationship can be confusing, because you might expect it to be between types, but it is ONE LEVEL UP from that, it is subtyping between KINDS!

Notes
Hardware values are always quoted, while our universes have coercive subtyping
EG: The Bit type can be coerced to ^(Val Bit).
Bit : VType : Kind
Val Bit : Type : Kind
^(Val Bit) : Kind
0 always stands for a quoted zero, so it has type ^(Val Bit).
Many quoted hardware values can be coerced to corresponding meta-level values.
When we check a hardware object against a corresponding meta-level type, the coercion "eta longs" the hardware object.
Example:
objects of type (a -> b) can be coerced to (a => b) 
mod x => y : a => b
mod x => y : a -> b   — works because mod is coerced to 
What other coercions do we have?
hardware-level values are eliminated at runtime, meta-level values are eliminated at compile time.
We infer, from the 
the meta level evaluates away


our CORE language

H {
}

M {
}

fun_h =>
fun_m =>


def flip := H {
  mod x => x match 0 => 1 | 1 => 0
}


2ltt flip := '(
  
)

prim_xor : ^(M(Bit -> M(Bit -> S(Bit)))
def xor := mod x y => prim_xor x y

prim_thing : ^(M(Bit -> S(Bit)) => ( ^(S(Bit)) => ^(S(Bit)) )
prim_thing := M {
  fun m =>
    fun x =>
     H { m x }
}

2ltt prim_thing :=
  fun m =>
    fun x =>
      '(~m ~x)

def prim_thing[m: Bit -> Bit](x

fun [a] =>
  fun (x) =>

def vec.map{a, n}(xs: vec[a, n]){b}[f: a -> b] :=
  n match {
  }  

let x := y in

thing2 := M {
  (prim_thing prim_xor) 1
}

def foo : fun f => mod x => h {f x}
def foo : mod x => m {f x}

'(f x)

~(f x)




def Decoupled[A: SignalType]: ModuleType :=
  (ready : Bit) -> Valid[A]

def Decoupled.fire (
sig Decoupled {
  t : Signal
  valid : t -> bit
  ready : 


def Decoupled[f](data, ready : Bit) : Bit
  when ready:
     f data
  return false


def Thing := 
  Decoupled (mod x => 

Decoupled {
  flip ready : UInt<1>
  data : Type
  valid : UInt<1> 
}


module Foo:
  input d : Decoupled
  output o : UInt<8>
  clock : Clock
  reg r, clock
  r <= 0
  when r == 0
    r <= 1

  when r == 0
     r <= 1
  else
     r <= 0

  r <= mux(r, 0, 1)

  d.ready <= r

  when d.valid && r
    o <= d.data
  else
    o <= x

ns Decoupled
  enum Valid[A: SignalType] {
    valid(data: A),
    invalid,
  }

  def Producer[A: SType]: MType :=
    (Ready) -> Valid[A]
  
  def Consumer[A: SType]: MType :=
    (Valid[A]) -> Ready
end

struct Foo.Output where
  ready: Bit,
  data: UInt[8],


def Foo(input: Decoupled.Valid[uint[8]]): Foo.Output :=
  Foo.Output {
    ready := reg[0](not(ready)),
    data := input match {
      | invalid      => zzz
      | valid(value) =>
        if ready
        then value
        else zzz
    }
  }

def Foo(input: Decoupled.Valid[Uint[8]]): Foo.Output where
  ready := reg[0](not(r)),
  value := input match {
    | invalid      => zzz
    | valid(value) =>
      if ready
      then value
      else zzz
  }

def delay[n : Nat]{A}(x : A): A :=
  n match {
    .succ n’ => reg[0](delay[n’](x))
    .zero    => x
  }

^(M(Bit -> S(Bit)) : Type

tcon Option{U}[T : U]: U where
  Some[T]: Option[T]
  None: Option[T]

def foo[t : Option Bit](m : Option Bit) :=

def foo (s : Option[Bit]): Option[Bit] := s
def foo : ^(M(Option[Bit] -> S(Option[Bit])))

def foo[x : Bit](y : Bit) := x + y
def bar(z : Bit) := foo[z](z)


module foo_j8j1td7(input y, output o)
  o <= z+y
endmodule;

module bar(input z, output o)
  o <= z + z
endmodule

def bar := '(
  mod "bar" (z:bit) =>
   (mod "foo" (y:bit) => z + y) z
)

module foo(input y, z, output o)
endmodule

module bar(input z, output o)
  foo(z, z, o2)
  o <= o2
endmodule()

def Bar{c : ClockDomain}(ready: Bit[c]): Decoupled.Valid[c, Uint[8]]:=
  let valid = 0;
  if ready = delay[10](valid)
  // increment the data
  let data = reg[0](data) + 1
  let valid = mux(reg[0](valid), 1, 0)
  if ready & valid
  then Decoupled.Valid.valid(data)
  else Decoupled.Valid.invalid

def Parent where
  foo := Foo bar
  bar := Bar foo


  { (x: Nat) =>
  foo
