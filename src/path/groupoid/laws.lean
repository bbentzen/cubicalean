/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ...core.path ..induction ..function .ops

open interval path 

-- basic notation for inv and comp

notation p `⁻¹` := path.inv _ p
infix `∙`:80 := path.comp _

-- non-dependent groupoid laws (proven by path induction)

variables {A : Type} (kan : Π A, has_hcom2 A)

def inv.refl {a : A} :
  path (path A a a) (refl a) (inv (kan A).has1 (refl a)) :=
begin
  fapply path.abs, intro j,
  fapply path.abs, intro i,
  { exact inv.filler (kan A).has1 (refl a) j i },
  { apply function.funext_iff.1 ((kan A).has1.t0 _) },
  { apply function.funext_iff.1 ((kan A).has1.t1 _) },
  { transitivity, apply pathdp.abs.eq ((kan A).has1.lid _),
    unfold path.refl, apply abs_irrel' (refl a) },
  { transitivity, apply pathdp.abs.eq rfl,
    apply abs_irrel' (refl a) }
end

def comp.refl {a : A} :
  path (path A a a) (refl a) (path.comp (kan A).has1 (refl a) (refl a)) :=
begin
  fapply path.abs, intro j,
  fapply path.abs, intro i,
  { exact comp.filler (kan A).has1 (refl a) (refl a) j i },
  { apply function.funext_iff.1 ((kan A).has1.t0 _) },
  { apply function.funext_iff.1 ((kan A).has1.t1 _) },
  have : comp.filler ((kan A).has1) (refl a) (refl a) i0 = λ i, a := (kan A).has1.lid _,
  { transitivity, apply pathdp.abs.eq this,
    unfold path.refl, apply abs_irrel' (refl a) },
  { transitivity, apply pathdp.abs.eq rfl,
    apply abs_irrel' (refl a) }
end

def inv.lc {a b : A} {p : path A a b} (kan' : Π U, coe.has_coe U) :
  path (path A a a) (refl a) (comp (kan A).has1 p (inv (kan A).has1 p)) :=
begin
  apply path.induction (kan A) (kan') p,
  apply path.comp (kan _).has1,
  { apply comp.refl kan },
  { apply ap, apply inv.refl kan }
end

def inv.rc {a b : A} {p : path A a b} (kan' : Π U, coe.has_coe U) :
  path (path A b b) (refl b) (comp (kan A).has1 (inv (kan A).has1 p) p) :=
begin
  apply path.induction (kan A) (kan') p,
  apply path.comp (kan _).has1,
  { apply comp.refl kan },
  { apply ap (λ p, comp ((kan A).has1) p (refl a)), apply inv.refl kan }
end

def inv.invo {a b : A} {p : path A a b} (kan' : Π U, coe.has_coe U) :
  path (path A a b) p (inv (kan A).has1 (inv (kan A).has1 p)) :=
begin
  apply path.induction (kan A) (kan') p,
  apply path.comp (kan _).has1,
  { apply inv.refl kan },
  { apply ap, apply inv.refl kan }
end

def comp.ru {a b : A} {p : path A a b} (kan' : Π U, coe.has_coe U) :
  path (path A a b) p (comp (kan A).has1 p (path.refl b)) :=
by apply path.induction (kan A) (kan') p; apply comp.refl

def comp.lu {a b : A} {p : path A a b} (kan' : Π U, coe.has_coe U) :
  path (path A a b) p (comp (kan A).has1 (refl a) p) :=
by apply path.induction (kan A) (kan') p; apply comp.refl

def comp.assoc {a b c d : A} {p : path A a b} {q : path A b c} {r : path A c d} (kan' : Π U, coe.has_coe U) :
  path (path A a d) (comp (kan A).has1 p (comp (kan A).has1 q r)) (comp (kan A).has1 (comp (kan A).has1 p q) r) :=
begin
  apply path.induction (kan A) (kan') r,
  apply path.transport kan', 
  { apply comp.ru kan kan' },
  { apply ap, apply inv (kan _).has1, apply comp.ru kan kan' }
end