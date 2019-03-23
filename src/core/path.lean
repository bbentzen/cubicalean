/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .kan

open interval

-- dependent and non-dependent path types

structure pathd {n : ℕ} (A : I → n-Type) (a : n-(A i0)) (b : n-(A i1)) :=
(p : (n+1)-A) (p0 : p i0 = a) (p1 : p i1 = b)

namespace pathd

def pathd.abs {n} {A : I → n-Type} (p : (n+1)-A) : pathd A (p i0) (p i1) :=
pathd.mk p rfl rfl 

def pathd.app {n : ℕ} (A : I → n-Type) (a : n-(A i0)) (b : n-(A i1))
  (p : pathd A a b) : (n+1)-A :=
pathd.rec (λ p _ _, p) p 

end pathd

def path {n : ℕ} (A : n-Type) (a : n-A) (b : n-A) := pathd (λ _, A) a b

-- non-dependent inversion and composition of lines

def path.inv {A : 0-Type} {a b : A} {kan : has_hcom A} :
  path A a b → path A b a :=
begin
  intro p, induction p with p p0 p1,
  rw p0.symm, rw p1.symm,
  fapply pathd.mk,
  { apply (hcom (λ _, p i0) [[ p ; (λ _, p i0) ]] kan) i1 },
  { transitivity, apply kan.eq0, simp }, 
  { transitivity, apply kan.eq1, simp }
end

def path.comp {A : 0-Type} {a b c : A} {kan : has_hcom A} :
  path A a b → path A b c → path A a c :=
begin
  intro p, induction p with p p0 p1,
  rw p0.symm, rw p1.symm,
  intro q, induction q with q q0 q1,
  rw q1.symm,
  fapply pathd.mk,
  { apply (kan.hcom (horn1.mk p (λ _, p i0) q rfl q0.symm)) i1 },
  { transitivity, apply kan.eq0, simp },
  { transitivity, apply kan.eq1, simp }, 
end
