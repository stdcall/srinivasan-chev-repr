#import "main-defs.typ": *
#import "statements.typ": *

#source(5, printed: "V")
#heading(level: 1, numbering: none)[Introduction] <front:introduction>

The aim of these notes is to give a survey of the main developments in the
theory of “ordinary”, i.e. characteristic 0 representations of finite Chevalley
groups which have occurred in recent years. In the year 1969–70 a seminar on
finite groups arising from algebraic groups was held at the Institute for
Advanced Study. In this seminar T.~A.~Springer gave some lectures on
Harish-Chandra's philosophy of cusp forms, which had at that time been applied
also to these finite groups. Springer then stated the so called “Macdonald
conjectures” which predicted that there would be families of representations of
these groups parametrized by the characters of the various “maximal tori”. An
important breakthrough came in 1976 when Lusztig and Deligne in their famous
paper [@bib:Deligne1976] published a proof of these conjectures, by constructing
virtual representations of the groups on the $ell$-adic cohomology of certain
varieties.

An outline of the contents is as follows. Chapter @ch:algebraic-groups is a
review of the main results that we need on the “absolute theory” of reductive
algebraic groups over an algebraically closed field. In Chapter
@ch:classification-of-tori and in the rest of the notes we consider the
situation where $G$ is a connected reductive group defined over $FF_q$, and
where $F$ is a Frobenius endomorphism of $G$. The group $G^F$ of fixed points
under $F$ is the finite group whose representation theory will be studied. The
classification of the maximal tori of $G^F$ is described, leading us to the
problem of constructing a family of virtual representations of
#source(6, printed: "VI")
$G^F$ corresponding to each torus. In Chapter @ch:principal-series this is done
in the easiest case, i.e. the case of the “split torus”, leading to the
principal series representations. In Chapter @ch:harish-chandra the theory of
Harish-Chandra is described and this brings out the importance of constructing
cuspidal (discrete series) representations.

Chapter @ch:ell-adic-cohomology is perhaps the raison d'être for these notes. In
recent years I have detected a growing dissatisfaction among finite group
theorists about assuming the existence and main properties of $ell$-adic
cohomology on an axiomatic basis. I have therefore endeavored in this chapter,
starting from a brief review of the classical theory of sheaves on a topological
space and of sheaf cohomology, to give an idea of how $ell$-adic cohomology
groups are constructed and to give a feeling for their properties by pointing
out classical analogues when possible. It is hoped that this chapter will be of
independent interest.

Chapter @ch:lusztig-deligne contains the main results in the paper of Lusztig
and Deligne. If $T$ is an $F$-stable maximal torus of $G$, a virtual
representation $R_T^(G)(theta)$ of $G^F$ is constructed corresponding to each
character $theta$ of $T^F$ (i.e. homomorphism of $T^F$ into
$overline(QQ)_ell^*$, where $ell$ is different from $p$, the characteristic of
$FF_q$). If $theta$ is regular, i.e. not fixed by any non-trivial element of
$N(T)^F / T^F$, then $R_T^(G)(theta)$ is irreducible, up to sign.

Orthogonality properties of the $R_T^(G)(theta)$ are established, and their
dimensions are computed. The connection between this theory and the
Harish-Chandra theory is established; in
#source(7, printed: "VII")
particular if $T$ is a “minisotropic torus” and $theta$ is a regular character
of $T^F$ then $plus.minus R_T^(G)(theta)$ is cuspidal (but not all cuspidal
representations arise this way). The proof of an important result in the paper
[@bib:Deligne1976] (@th:lefschetz-jordan-decomposition of these notes) which
leads to a reduction formula for the character values of the $R_T^(G)(theta)$
has so far been inaccessible to many group theorists because of the technical
machinery involved. I have described the main ideas in this proof, omitting some
of the details, and to my mind this is the most interesting feature of this
chapter. The rest of the material follows either the Lusztig-Deligne paper
[@bib:Deligne1976] or the monograph of Lusztig [@bib:Lusztig1978].

The determination of the explicit values of the characters of the
$R_T^(G)(theta)$ remains one of the main unsolved problems in the theory. The
work of Springer and Kazhdan which enables us to write down the values at
unipotent elements in terms of “trigonometric sums” on the Lie algebra (provided
$p$ and $q$ are large) is described in Chapter @ch:characters. Finally in
Chapter @ch:classification-of-representations I have tried to bring the material
up-to-date by describing recent work of Lusztig on the classification of
representations of classical groups and of “unipotent” representations for all
types. This chapter also contains a section on Hecke algebras i.e. centralizer
algebras of the representations of $G^F$ induced from certain representations of
parabolic subgroups. These algebras arise naturally when we try to decompose
these induced representations.

The notes are intended to be accessible to advanced
#source(8, printed: "VIII")
graduate students. A knowledge of the representation theory of finite groups to
the extent of say, Parts I and II of the book by Serre [@bib:Serre1977a] is
assumed; some knowledge of algebraic groups is desirable but not absolutely
necessary. In Chapters @ch:classification-of-tori through @ch:characters I have
given proofs of most of the results; Chapter
@ch:classification-of-representations is essentially a review of recent results
but I have included some discussions of proofs. The bibliography includes mainly
the papers that I have quoted in the notes. For supplementary references the
reader can consult a survey article by Curtis [@bib:Curtis1979].

#heading(level: 2, numbering: none)[Acknowledgments] <front:acknowledgments>

It is a pleasure to thank the Mathematics Department of the University of
Illinois, Chicago Circle, for their warm hospitality during the Fall Quarter of
1978–79, when I gave the lectures which formed a base for these notes. In
particular I thank the members of my audience, especially a “hard core”
consisting of Paul Fong, Noboru Ito, Cary Huffman, Mark Ronan and Stephen Smith,
for their stimulating comments and for their encouragement of me to publish
these notes.

An initial version of the notes was written while I was a visitor to the
University of Chicago in December 1978. I thank the Mathematics Department,
especially Paul Sally and Jonathan Alperin, for their hospitality during this
period. At this time I had several illuminating conversations with Spencer Bloch
which helped me to understand the material in Chapter @ch:ell-adic-cohomology,
and it is a pleasure to thank him for this. A
#source(9, printed: "IX")
preliminary draft of Chapter @ch:ell-adic-cohomology was read by Michael Artin
who made many valuable suggestions.

I owe a great debt to George Lusztig, who has generously shared with me his time
and his ideas during the last few years. His beautiful papers have led me into
new worlds whose existence I was only dimly aware of earlier. I was helped in
overcoming my initial trepidation at entering these worlds by conversations
with, and encouragement from, David Kazhdan.

I would also like to record here my gratitude to my colleagues Robert Kilmoyer,
Edward Cline and John Kennison, who have provided me through the years with
mathematical stimulation, friendship, support, and a happy family atmosphere in
the Department. It is also a pleasure to thank Theresa Shusas who has
single-handedly run the Department with a rare combination of efficiency and
good humor; in particular I thank her for the fine job she has done of typing a
part of these notes. A major part of the notes was typed by Margaret Jaquith who
stepped in when time was short and did an excellent job.

Finally I thank the National Science Foundation for financial support in the
form of Grant MCS-78-02184.

Bhama Srinivasan

Clark University \
Worcester, MA
