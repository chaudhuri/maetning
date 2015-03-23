(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

class namegen_core =
  object
    val mutable last = 0
    method step = last <- last + 1
    method reset = last <- 0
  end

class ['a] namegen (fn : int -> 'a) =
  object (self : 'self)
    inherit namegen_core as super
    method next = super#step ; fn last
  end

class ['a, 'b] namegen1 (fn : int -> 'a -> 'b) =
  object (self : 'self)
    inherit namegen_core as super
    method next x = super#step ; fn last x
  end

class ['a, 'b, 'c] namegen2 (fn : int -> 'a -> 'b -> 'c) =
  object (self : 'self)
    inherit namegen_core as super
    method next x y = last <- last + 1 ; fn last x y
  end
