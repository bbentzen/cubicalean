/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .connections .groupoid

--TODO: clean this up, relocate defs

open interval pathd

def transport {A : Type} {a x y : A} (h : x = y) 
   (p : path A a x) : (path A a y) := 
eq.rec p h

lemma family_eq {A : Type} {a : A} {C : Π x : A, path A a x → Type} 
              (x : A) (p : path A a a) (q : path A a x) (h : a = x) (h' : transport h p = q) :
  C a p = C x q :=
begin
  revert h', unfold transport,
  induction h, simp, intro, induction h', refl 
end

lemma transport_abs {A : Type} {a x y : A} (h : x = y) (p : I → A) (h0 : p i0 = a ) (hx : p i1 = x) (hy : p i1 = y) :
  transport h (path.abs p h0 hx ) = path.abs p h0 hy := 
by unfold transport; induction h; simp

lemma trans_refl_meet {A : Type} {a b : A} (kan : has_hcom2 A) (p : path A a b) :
  transport ((path.app0 p).symm) (path.refl a) = 
  path.abs (meet kan (app p) i0) 
    (eq.trans (meet.face0j0i kan (app p)) (path.app0 p)) 
    (eq.trans (meet.face0j1i kan (app p)) rfl) :=
begin
  rw refl.eq (eq.trans (meet.face0j kan (app p)) (funext (λ i, path.app0 p) )), 
  apply transport_abs, 
  transitivity,
  apply meet.face0j1i kan (app p), apply path.app0
end

lemma family_i0 {A : Type} {a : A} {C : Π x : A, path A a x → Type} (kan : has_hcom2 A) 
  (kan' : Π U, coe.has_coe U) 
  (x : A) (p : path A a x) : 
  C a (path.refl a) = 
  C (p @@ i0) (path.abs (meet kan (app p) i0) 
    (eq.trans (meet.face0j0i kan (app p)) (path.app0 p)) 
    (eq.trans (meet.face0j1i kan (app p)) rfl ) ) :=
begin
  fapply family_eq,
  apply (path.app0 p).symm,
  apply trans_refl_meet
end

lemma family_eq2 {A : Type} {a x y: A} {C : Π x : A, path A a x → Type} 
              (p : path A a x) (q : path A a y) (h : x = y) (h' : transport h p = q) :
  C x p = C y q :=
begin
  revert h', unfold transport,
  induction h, simp, intro, induction h', refl 
end

lemma trans_eta {A : Type} {a b x : A} (h : b = x) (p : path A a b) (ha : p @@ i0 = a) (hx : p @@ i1 = x) :
  transport h p = path.abs (path.app p) ha hx :=
begin
  unfold transport,
  induction h, simp, 
  symmetry,
  apply pathdp.eta
end

lemma trans_eta' {A : Type} {a b : A} (p : path A a b) (hb : b = p @@ i1) (ha : p @@ i0 = a) (hr : p @@ i1 = p @@ i1) :
  transport hb p = path.abs (app p) ha hr := 
by apply trans_eta

lemma trans_p_meet1 {A : Type} {a b : A} (kan : has_hcom2 A) (p : path A a b)
      (ha : meet kan (app p) i1 i0 = a) (hb : meet kan (app p) i1 i1 = p @@ i1) :
  transport ((app1 p).symm) p = 
  path.abs (meet kan (path.app p) i1) ha hb :=
begin
  revert ha hb, refine eq.rec _ (meet.face1j kan (app p)).symm,
  intros, apply trans_eta'
end

lemma trans_p_meet {A : Type} {a b : A} (kan : has_hcom2 A) (p : path A a b) :
  transport ((path.app1 p).symm) p = 
  path.abs (meet kan (app p) i1) 
    (eq.trans (meet.face1j0i kan (app p)) (path.app0 p)) 
    (eq.trans (meet.face1j1i kan (app p)) rfl) :=
begin
  symmetry, apply abs_irrel, symmetry, apply trans_p_meet1,
  apply (eq.trans (meet.face1j0i kan (app p)) (path.app0 p)),
  apply (eq.trans (meet.face1j1i kan (app p)) rfl)
end

lemma family_i1 {A : Type} {a : A} {C : Π x : A, path A a x → Type} (kan : has_hcom2 A) 
              (kan' : Π U, coe.has_coe U) (x : A) (p : path A a x) : 
  C x p = C (p @@ i1) (path.abs (meet kan (app p) i1) 
          (eq.trans (meet.face1j0i kan (app p)) (path.app0 p)) 
          (eq.trans (meet.face1j1i kan (app p)) rfl)) :=
begin
  apply family_eq2,
  apply trans_p_meet kan
end

lemma coe_u {A : Type} {a : A} {C : Π x : A, path A a x → Type} (kan : has_hcom2 A) 
  (kan' : Π U, coe.has_coe U) 
  (x : A) (p : path A a x) (u : C a (path.refl a)) : 
  C (p @@ i0) (path.abs (meet kan (app p) i0) 
    (eq.trans (meet.face0j0i kan (app p)) (path.app0 p)) 
    (eq.trans (meet.face0j1i kan (app p)) rfl ) ) :=
(eq.mp (family_i0 kan kan' x p) u)

theorem path_ind {A : Type} {a : A} {C : Π x : A, path A a x → Type} (kan : has_hcom2 A) (kan' : Π U, coe.has_coe U) : 
  Π (x : A) (p : path A a x) (u : C a (path.refl a)), C x p :=
λ x p u, eq.mp (family_i1 kan kan' x p).symm 
((kan' (λ i, C (p @@ i) (path.abs (meet kan (app p) i) 
(eq.trans (meet.face0i' kan (app p) i) (app0 p) ) (meet.face1i' kan (app p) i) ))).coe 
i0 (eq.mp (family_i0 kan kan' x p) u) i1)