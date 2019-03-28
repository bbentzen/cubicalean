/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

lemma funext_iff {A B : Type} {f g : A → B} : 
  f = g ↔ ∀ x, f x = g x :=
iff.intro (λ h, eq.rec (λ _, rfl) h) funext
