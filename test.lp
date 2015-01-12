f(c).
q:- f(X), not p, not r.
p :-f(X), not q, not r.
r :-f(X), not p, not q.
:- r.


%redundancy
p :-f(X), not q, not r.
f:-q.