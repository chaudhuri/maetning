%--------------------------------------------------------------------------
% File     : SYN918+1 : ILTP v1.1.2
% Domain   : Syntactic
% Problem  : From Smullyan
% Version  : Especial.
% English  : 

% Refs     : [Smu68] Smullyan (1968), First-Order Logic
%            [Shu04] Shults (2004), Email to G. Sutcliffe
% Source   : [Shu04]
% Names    :

% Status   : Theorem
% Rating   : 0.11 v3.1.0
%
% Status (intuit.) : Open
% Rating (intuit.) : 1.00 v1.1.0
%
% Syntax   : Number of formulae    :    1 (   0 unit)
%            Number of atoms       :   15 (   0 equality)
%            Maximal formula depth :    8 (   8 average)
%            Number of connectives :   16 (   2 ~  ;   1  |;   6  &)
%                                         (   0 <=>;   7 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-1 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    6 (   0 singleton;   4 !;   2 ?)
%            Maximal term depth    :    1 (   1 average)

% Comments : 
%--------------------------------------------------------------------------
fof(prove_this,refute,
    ( ( ! [X] : 
          ( ( ( f(X)
              & g(X) )
           => h(X) )
         => ? [Y] : 
              ( f(Y)
              & ~ g(Y) ) )
      & ( ! [W] : 
            ( f(W)
           => g(W) )
        | ! [Z] : 
            ( f(Z)
           => h(Z) ) ) )
   => ( ! [R] : 
          ( ( f(R)
            & h(R) )
         => g(R) )
     => ? [V] : 
          ( f(V)
          & g(V)
          & ~ h(V) ) ) )).

%--------------------------------------------------------------------------
