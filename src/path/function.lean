/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..core.path

open pathd interval

namespace path

lemma ap {A B : Type} (f : A → B) {a b : A} :
  path A a b → path B (f a) (f b) :=
λ p, path.abs (λ i, f (p @@ i))
(by rw app0) (by rw app1)

lemma apd {A : Type} {B : A → Type} {f : Π x, B x} {a b : A} :
  Π p : path A a b, pathd (λ i, B (p @@ i)) (f (p @@ i0)) (f (p @@ i1)) :=
λ p, pathd.abs (λ i, f (p @@ i))
(by rw app0) (by rw app1)

theorem funext {A B : Type} {f g : A → B} : 
  (∀ x, path B (f x) (g x)) → path (A → B) f g :=
λ h, path.abs (λ i x, ((h x) @@ i))
(funext (λ x, app0 (h x))) (funext (λ x, app1 (h x)))

end path

