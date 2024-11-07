---- MODULE MC ----
EXTENDS VectorClocks, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions P
const_1730944971194193000 == 
{p1, p2, p3}
----

\* SYMMETRY definition
symm_1730944971194194000 == 
Permutations(const_1730944971194193000)
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1730944971194195000 ==
{0,1,2,3}
----
\* Constant expression definition @modelExpressionEval
const_expr_1730944971195196000 == 
LET R == {<<p1,p2>>} IN
TransitiveClosure(R)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1730944971195196000>>)
----

=============================================================================
\* Modification History
\* Created Wed Nov 06 18:02:51 PST 2024 by nano
