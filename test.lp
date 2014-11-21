f.
q:- f, not p, not r.
p :-f, not q, not r.
r :-f, not p, not q.
:- r.


%redundancy
p :-f, not q, not r.
f:-q.