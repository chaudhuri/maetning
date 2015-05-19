%--------------------------------------------------------------------------
% File     : SYN917+1 : ILTP v1.1.2
% Domain   : Syntactic
% Problem  : Combined problems from Smullyan
% Version  : Especial.
% English  : 

% Refs     : [Smu68] Smullyan (1968), First-Order Logic
%            [Shu04] Shults (2004), Email to G. Sutcliffe
% Source   : [Shu04]
% Names    :

% Status   : Theorem
% Rating   : 0.78 v3.1.0
%
% Status (intuit.) : Open
% Rating (intuit.) : 1.00 v1.1.0
%
% Syntax   : Number of formulae    :    1 (   0 unit)
%            Number of atoms       :   94 (   0 equality)
%            Maximal formula depth :   23 (  23 average)
%            Number of connectives :   98 (   5 ~  ;   8  |;  39  &)
%                                         (  10 <=>;  36 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    7 (   1 propositional; 0-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :   56 (   2 singleton;  34 !;  22 ?)
%            Maximal term depth    :    1 (   1 average)

% Comments : 
%--------------------------------------------------------------------------
fof(prove_this,refute,
    ( ( ( ! [X] : 
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
            & ~ h(V) ) ) )
    & ( ( ! [X,Y] : 
            ( r(X,Y)
           => r(Y,X) )
        & ! [X,Y,Z] : 
            ( ( r(X,Y)
              & r(Y,Z) )
           => r(X,Z) ) )
     => ! [X,Y] : 
          ( r(X,Y)
         => r(X,X) ) )
    & ( ( ( ! [X] : 
              ( ( f(X)
                & g(X) )
             => h(X) )
         => ? [X] : 
              ( f(X)
              & ~ g(X) ) )
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
            & ~ h(V) ) ) )
    & ? [X] : 
      ! [Y] : 
        ( ( p(Y)
         => q(X) )
       => ( p(X)
         => q(X) ) )
    & ( ! [X] : 
          ( p(X)
          & q(X) )
    <=> ( ! [X] : p(X)
        & ! [X] : q(X) ) )
    & ( ( ! [X] : p(X)
        | ! [X] : q(X) )
     => ! [X] : 
          ( p(X)
          | q(X) ) )
    & ( ? [X] : 
          ( p(X)
          | q(X) )
    <=> ( ? [X] : p(X)
        | ? [X] : q(X) ) )
    & ? [Y] : 
        ( p(Y)
       => ! [X] : p(X) )
    & ( ? [X] : 
          ( p(X)
          & q(X) )
     => ( ? [X] : p(X)
        & ? [X] : q(X) ) )
    & ! [Y] : 
        ( ! [X] : p(X)
       => p(Y) )
    & ( ! [X] : p(X)
     => ? [X] : p(X) )
    & ( ~ ( ? [Y] : p(Y) )
     => ! [Y] : 
          ( ? [X] : p(X)
         => p(Y) ) )
    & ( ! [X] : 
          ( p(X)
          | c )
    <=> ( ! [X] : p(X)
        | c ) )
    & ( ? [X] : 
          ( p(X)
          & c )
    <=> ( ? [X] : p(X)
        & c ) )
    & ( ? [X] : c
    <=> c )
    & ( ! [X] : c
    <=> c )
    & ( ? [X] : 
          ( c
         => p(X) )
    <=> ( c
       => ? [X] : p(X) ) )
    & ( ? [X] : 
          ( p(X)
         => c )
    <=> ( ! [X] : p(X)
       => c ) )
    & ( ! [X] : 
          ( c
         => p(X) )
    <=> ( c
       => ! [X] : p(X) ) )
    & ( ! [X] : 
          ( p(X)
         => c )
    <=> ( ? [X] : p(X)
       => c ) ) )).

%--------------------------------------------------------------------------
