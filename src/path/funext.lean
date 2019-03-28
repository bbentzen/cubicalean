/-
Copyright (c) 2019 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..core.path

open pathd

namespace path

def funext {A B : Type} {f g : A → B} : 
  (∀ x, path B (f x) (g x)) → path (A → B) f g :=
λ h, path.abs (λ i x, ((h x) @@ i))
(funext (λ x, app0 (h x)))
(funext (λ x, app1 (h x)))

end path