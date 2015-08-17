f(a).
f(b).
f(c).
f(d).
f(e).
f(f).
f(g).
f(h).
f(i).



q(X):- f(X), not p(X), not r(X).
p(X) :-f(X), not q(X), not r(X).
r(X) :-f(X), not p(X), not q(X).
%:- r(X).
