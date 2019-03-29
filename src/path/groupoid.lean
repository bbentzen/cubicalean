/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..core.path ..path.connections

open interval

-- non-dependent inversion and composition of lines

namespace path

def refl {A : Type} (a : A) : path A a a :=
path.abs (λ _, a) rfl rfl 

def inv {A : Type} {a b : A} {kan : has_hcom A} :
  path A a b → path A b a :=
begin
  intro p, induction p with p _ _ p0 p1,
  unfold eq.mp at *; simp at *,
  rw p0.symm, rw p1.symm,
  fapply pathdp.abs,
  { apply (hcom (λ _, p i0) [[ p ; (λ _, p i0) ]] kan) i1 },
  repeat { reflexivity },
  { transitivity, apply kan.eq0, unfold eq.mp; simp },
  { transitivity, apply kan.eq1, unfold eq.mp; simp }
end

def comp {A : Type} {a b c : A} {kan : has_hcom A} :
  path A a b → path A b c → path A a c :=
begin
  intro p, induction p with p _ _ p0 p1,
  unfold eq.mp at *; simp at *,
  rw p0.symm, rw p1.symm,
  intro q, induction q with q _ _ q0 q1,
  unfold eq.mp at *; simp at *,
  rw q1.symm,
  fapply pathdp.abs,
  { apply (kan.hcom (horn1.mk p (λ _, p i0) q rfl q0.symm)) i1 },
  repeat { reflexivity },
  { transitivity, apply kan.eq0, unfold eq.mp; simp },
  { transitivity, apply kan.eq1, unfold eq.mp; simp }, 
end

end path

namespace refl

open path

lemma eq {A : Type} {a : A} {p : I → A} (h : p = λ _, a ) {h0 : p i0 = a } {h1 : p i1 = a} : 
  path.refl a = path.abs p h0 h1 :=
by cases h; refl

lemma meet {A : Type} {a b : A} (kan : has_hcom2 A) (p : path A a b) :
  path.refl a = 
  path.abs (meet kan (app p) i0) 
    (eq.trans (meet.face0j0i kan (app p)) (path.app0 p)) 
    (eq.trans (meet.face0j1i kan (app p)) (path.app0 p)) :=
begin
  apply eq,
  transitivity,
  apply meet.face0j kan (app p),
  apply funext, intro, apply path.app0
end

end refl 