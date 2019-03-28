/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .kan

open interval

-- propositional dependent path type (type equality up to propositional equality)

inductive pathdp (A : I → Type) {A0 A1 : Type} (a : A0) (b : A1) : Type
| abs (p : Π i, A i) (ha : A0 = A i0) (hb : A1 = A i1)
      (p0 : p i0 = eq.rec a ha) (p1 : p i1 = eq.rec b hb) : pathdp

namespace pathdp

@[reducible] def app {A : I → Type} {A0 A1 : Type} {a : A0} {b : A1} 
  (p : pathdp A a b) (i : I) : A i :=
by induction p with p; exact p i --pathdp.rec (λ p _ _ _ _, p i) p

def beta {A : I → Type} {A0 A1 : Type} {a : A0} {b : A1} (p : Π i, A i)
         {ha : A0 = A i0} {hb : A1 = A i1}
         (p0 : p i0 = eq.mp ha a) (p1 : p i1 = eq.mp hb b) : 
  Π i, app (pathdp.abs p ha hb p0 p1) i = p i :=
by intro i; unfold app

def beta' {A : I → Type} {A0 A1 : Type} {a : A0} {b : A1} (p : Π i, A i)
          {ha : A0 = A i0} {hb : A1 = A i1}
          (p0 : p i0 = eq.mp ha a) (p1 : p i1 = eq.mp hb b) : 
  app (pathdp.abs p ha hb p0 p1) = p :=
by funext; apply beta

def eta {A : I → Type} {A0 A1 : Type} {a : A0} {b : A1} (p : pathdp A a b)
        (ha : A0 = A i0) (hb : A1 = A i1) 
        (p0 : app p i0 = eq.rec a ha) (p1 : app p i1 = eq.rec b hb) : 
  pathdp.abs (app p) ha hb p0 p1 = p :=
by induction p; simp; refl

infix ` @@ `:80 := app

def app_mono {A : I → Type} {A0 A1 : Type} {a : A0} {b : A1} (p q : pathdp A a b) :
  (λ i, p @@ i) = (λ i, q @@ i) → p = q :=
begin
  induction p, induction q,
  rw pathdp.beta', rw pathdp.beta',
  intro h, simp at h, induction h, refl
end

def abs_irrel {A : I → Type} {A0 A1 : Type} {a : A0} {b : A1} {p : Π i, A i} 
        (q : pathdp A a b)  {ha ha' : A0 = A i0} {hb hb' : A1 = A i1} 
        {p0 p0' : p i0 = eq.mp ha a} {p1 p1' : p i1 = eq.mp hb b} : 
  pathdp.abs p ha hb p0 p1 = q → pathdp.abs p ha' hb' p0' p1' = q  :=
by intro h; induction h; rw proof_irrel p0

def abseq {A : I → Type} {A0 A1 : Type} {a : A0} {b : A1} {p q : Π i, A i} 
        (h : p = q) {ha : A0 = A i0} {hb : A1 = A i1} 
        {p0 : p i0 = eq.mp ha a} {p1 : p i1 = eq.mp hb b} : 
  pathdp.abs p ha hb p0 p1 = pathdp.abs q ha hb (eq.rec p0 h) (eq.rec p1 h) :=
by induction h; simp

def eta.eq' {A : I → Type} {A0 A1 : Type} {a : A0} {b : A1} {p q : pathdp A a b} 
        (h : p = q) {ha : A0 = A i0} {hb : A1 = A i1} 
        {p0 : app p i0 = eq.mp ha a} {p1 : app p i1 = eq.mp hb b} : 
  pathdp.abs (λ i, p @@ i) ha hb p0 p1 = pathdp.abs (λ i, q @@ i) ha hb (eq.rec p0 h) (eq.rec p1 h) :=
by induction h; simp

def ty0 {A : I → Type} {A0 A1 : Type} {a : A0} {b : A1} 
  (p : pathdp A a b) : A0 = A i0  :=
pathdp.rec (λ p ha _ _ _, ha) p

def ty1 {A : I → Type} {A0 A1 : Type} {a : A0} {b : A1} 
  (p : pathdp A a b) : A1 = A i1  :=
pathdp.rec (λ p _ hb _ _, hb) p

def app0 {A : I → Type} {A0 A1 : Type} {a : A0} {b : A1} (p : pathdp A a b) :
  p @@ i0 = eq.mp (ty0 p) a :=
by induction p; apply p_p0

def app1 {A : I → Type} {A0 A1 : Type} {a : A0} {b : A1} (p : pathdp A a b) :
  p @@ i1 = eq.mp (ty1 p) b :=
by induction p; apply p_p1

def tyeq {A : I → Type} {A0 A1 : Type} {a : A0} {b : A1} (p : pathdp A a b) :
  pathdp A a b = pathdp A (p @@ i0) (p @@ i1) :=
by rw app0; rw app1; induction ty0 p; induction ty1 p; refl

def abs.eq {A : I → Type} {A0 A1 : Type} {a : A0} {b : A1} {p q : Π i, A i} (h : p = q) 
        {ha : A0 = A i0} {hb : A1 = A i1} (p0 : p i0 = eq.mp ha a) (p1 : p i1 = eq.mp hb b) : 
  pathdp.abs p ha hb p0 p1 = pathdp.abs q ha hb (eq.rec p0 h) (eq.rec p1 h) :=
by induction h; refl

end pathdp

-- exact dependent path type (type equality is exact)

def pathd (A : I → Type) (a : A i0) (b : A i1) := pathdp A a b

namespace pathd

def abs {A : I → Type} {a : A i0} {b : A i1} (p : Π i, A i)
  (p0 : p i0 = a) (p1 : p i1 = b) : pathd A a b :=
@pathdp.abs A (A i0) (A i1) _ _ p rfl rfl p0 p1

@[simp] def app {A : I → Type} {A0 A1 : Type} {a : A0} {b : A1} 
  (p : pathdp A a b) (i : I) : A i :=
pathdp.app p i

def eta {A : I → Type} {a : A i0} {b : A i1} (p : pathd A a b)
        (p0 : app p i0 = a) (p1 : app p i1 = b) : 
  abs (app p) p0 p1 = p :=
by apply pathdp.eta p rfl rfl p0 p1 

def app0 {A : I → Type} {a : A i0} {b : A i1} (p : pathdp A a b) :
  p @@ i0 = a :=
by induction p; apply p_p0

def app1 {A : I → Type} {a : A i0} {b : A i1} (p : pathdp A a b) :
  p @@ i1 = b :=
by induction p; apply p_p1

def tyeq {A : I → Type} {a : A i0} {b : A i1} (p : pathdp A a b) :
  pathd A a b = pathd A (p@@i0) (p@@i1) :=
by rw app0; rw app1

end pathd

-- non-dependent path types

def path (A : Type) (a : A) (b : A) := pathd (λ _, A) a b

namespace path

def abs {A : Type} {a b : A} (p : Π i, A) (p0 : p i0 = a) (p1 : p i1 = b) :
  path A a b :=
pathd.abs p p0 p1

@[simp] def app {A : Type} {a b : A} (p : path A a b) :
  I → A := 
pathdp.app p

def eta {A : Type} {a b : A} (p : path A a b) (p0 : app p i0 = a) (p1 : app p i1 = b) : 
  abs (app p) p0 p1 = p :=
pathd.eta p p0 p1

def app0 {A : Type} {a b : A} (p : path A a b) :
  p @@ i0 = a :=
pathd.app0 p

def app1 {A : Type} {a b : A} (p : path A a b) :
  p @@ i1 = b :=
pathd.app1 p

def tyeq {A : Type} {a b : A} (p : path A a b) : 
  path A a b = path A (p@@i0) (p@@i1) :=
by rw app0; rw app1

end path