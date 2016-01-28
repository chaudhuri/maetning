%%% PORGI examples

% The "easy" one from figure 10
% (A -> B) | (B -> C) | (C -> D) | (D -> E) | (E -> F) | (F -> A)

%refute (A => B) + (B => C) + (C => D) + (D => E) + (E => F) + (F => A).


% The "intermediate" one from figure 11
% (((~~P -> P) -> P | ~P) -> ~P | ~~P) -> ~~P | (~~P -> P)

%refute (((~ ~ p => p) => p + ~ p) => ~ p + ~ ~ p) => ~ ~ p + (~ ~ p => p).


% The "hard" one from figure 12
% ~~A | (A -> ~~B | (B -> ~~C | (C -> (~~D -> D) | ~D | ~~D)))

%refute ~ ~ a + (a => ~ ~ b + (b => ~ ~ c + (c => (~ ~ d => d) + ~ d + ~ ~ d))).