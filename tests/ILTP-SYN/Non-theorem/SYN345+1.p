%--------------------------------------------------------------------------
% File     : SYN345+1 : ILTP v1.1.2
% Domain   : Syntactic
% Problem  : Church problem 46.16 (4)
% Version  : Especial.
% English  : 

% Refs     : [Chu56] Church (1956), Introduction to Mathematical Logic I
% Source   : [Chu56]
% Names    : 46.16 (4) [Chu56]

% Status   : Theorem
% Rating   : 0.22 v3.1.0, 0.00 v2.5.0, 0.33 v2.4.0, 0.33 v2.2.1, 0.00 v2.1.0
%
% Status (intuit.) : Non-Theorem
% Rating (intuit.) : 0.75 v1.0.0
%
% Syntax   : Number of formulae    :    1 (   0 unit)
%            Number of atoms       :   12 (   0 equality)
%            Maximal formula depth :   11 (  11 average)
%            Number of connectives :   11 (   0 ~  ;   0  |;   1  &)
%                                         (   1 <=>;   9 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    1 (   0 propositional; 3-3 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    5 (   0 singleton;   3 !;   2 ?)
%            Maximal term depth    :    1 (   1 average)

% Comments : 
%--------------------------------------------------------------------------
fof(church_46_16_4,refute,
    ( ! [X1,X2] : 
      ? [Y1,Y2] : 
      ! [Z] : 
        ( ( ( big_f(X1,X2,Y1)
           => big_f(Y2,Y1,Z) )
         => ( big_f(X1,X1,X2)
           => big_f(X1,X2,X2) ) )
       => ( ( ( big_f(X2,Y1,Y2)
             => big_f(Y1,Z,Z) )
           => ( big_f(X1,X2,X2)
             => big_f(X1,X1,X2) ) )
         => ( big_f(Y1,Y2,Z)
           => ( big_f(X2,X2,Y1)
              & ( big_f(X1,X1,X2)
              <=> big_f(X1,X2,X2) ) ) ) ) ) )).

%--------------------------------------------------------------------------