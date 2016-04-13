%refute (p => p) => (p + ~ p).
%refute ((~ ~ a) => (b + c)) => (((~ ~ a) => b) + ((~ ~ a) => c)).
%refute ~ (a * b) => ~ a + ~ b.
%refute (~ a => ~ b) => b => a.
%refute (a => c) => (~ a => c) => c.
%refute (~ a => b) => (~ a => ~ b) => a.
       % positive a.
       % assume foo : a + ~a => c.
%refute (a + ~ a => c) => c.
%refute ~ ~ (a + b) => a + b.
%refute (a => (b + c)) => (a => b) + (a => c).
%refute (~ a => (b + c)) => (~ a => b) + (~ a => c).
%refute ~ a + ~ ~ a.
%refute ~ (~ ~ a + ~ a).

%%% The following are also classically false, which you can tell
%%% because their countermodels have only one world.

% refute a + (b * c) => (a + b) * c.
% refute (a => a) => ~ a.
