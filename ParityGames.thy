chapter \<open>Parity Games\<close>
theory ParityGames
imports Main
begin
subsection \<open>Parity Game Definitions\<close>
text \<open>
  An arena \<A> in parity games consists of a directed graph and sets of vertices with owners.
  It is defined as \<A> = (V,V0,V1,E) where
  - (V,E) is a directed graph
  - V0 and V1 = V\V0 are sets of vertices belonging to the two players
  - E \<subseteq> V \<times> V is a set of edges, such that every vertex has at least one successor
  The simplest way for us to represent this is as a directed graph of integers (which will be priorities),
  and a set of vertices belonging to player 0.
\<close>
text \<open>A directed graph is represented as a set of edges\<close>
type_synonym 'v dgraph = "('v\<times>'v) set"
definition succs :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> 'v set" where
  "succs E v \<equiv> E``{v}"
definition is_succ :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "is_succ E v w \<equiv> w \<in> succs E v"

lemma "\<forall>w \<in> succs E v. is_succ E v w"
  unfolding is_succ_def succs_def
  by auto

definition subgraph :: "'v dgraph \<Rightarrow> ('v\<times>'v) \<Rightarrow> 'v dgraph" where
  "subgraph E e \<equiv> E-{e}"

lemma "e \<notin> subgraph E e"
  unfolding subgraph_def by auto


locale arena_defs =
  fixes E :: "'v dgraph"
  fixes V\<^sub>0 :: "'v set"
  fixes prio :: "'v \<Rightarrow> nat"
begin  
  definition V where "V = fst`E \<union> snd`E"
  definition V\<^sub>1 where "V\<^sub>1 = V-V\<^sub>0"
end

text \<open>
  A play is an infinite sequence \<pi>\<in>V\<omega> of moves along the edges of the graph in the arena.
  A winning play for player 0 is a play where the maximum priority seen infinitely often is even.
\<close>
(*
datatype ('a) l = N | C "'a l" 'a "'a l"
print_theorems
term set_l
term map_l
term rel_l
term pred_l

lemma "pred_l P l \<longleftrightarrow> (\<forall>x\<in>set_l l. P x)"
  apply (induction l) apply auto done


lemma "(\<forall>x\<in>set_l l. R x (f x)) \<Longrightarrow> rel_l R l (map_l f l)"
  apply (induction l) apply auto done


term rec_l

*)
text \<open>We represent paths with an infinite coinductive list. 
  Still testing how this works. A lazy list might work better?\<close>
codatatype (infset: 'a) inflist = InfCons (head: 'a) (tail: "'a inflist")

definition iappend :: "'a list \<Rightarrow> 'a inflist \<Rightarrow> 'a inflist" where "iappend = foldr InfCons"

lemma [simp]: "iappend [] xs = xs" unfolding iappend_def by simp
lemma [simp]: "iappend (x#xs) ys = InfCons x (iappend xs ys)" unfolding iappend_def by simp

lemma "iappend (xs@ys) zs = iappend xs (iappend ys zs)"
  by (induction xs) auto


primcorec ireplicate :: "'a \<Rightarrow> 'a inflist" where
  "ireplicate x = InfCons x (ireplicate x)"

context 
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

  (*
  
    v\<^sub>0 v\<^sub>1 v\<^sub>2 \<dots>
    
    R v\<^sub>i v\<^sub>i\<^sub>+\<^sub>1
    
    path u (v#vs) \<longleftrightarrow> R u v \<and> path v vs
  *)

  coinductive is_ipath :: "'a \<Rightarrow> 'a inflist \<Rightarrow> bool" where
    "R u v \<Longrightarrow> is_ipath v vs \<Longrightarrow> is_ipath u (InfCons v vs)"

  find_theorems is_ipath  

lemma "R x x \<Longrightarrow> vs=ireplicate x \<Longrightarrow> is_ipath x vs"
  apply (coinduction)
  using ireplicate.code by fastforce
(*
    apply (rule is_ipath.coinduct[where X="\<lambda>x vs. R x x \<and> vs=ireplicate x"])
    apply simp
    apply simp
    subgoal for xx
      apply (rule exI[where x=xx])
      apply (rule exI[where x="ireplicate xx"])
      apply simp
      by (rule ireplicate.ctr)
    done
*)
(*
  primcorec pathmap :: "('b \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> 'b inflist \<Rightarrow> nat" where
    "pathmap f vs = f (head vs) (pathmap f (tail vs))"
  
  
  primcorec path :: "'a inflist \<Rightarrow> bool" where
    "path vs \<longleftrightarrow> undefined (path (tail vs))"

  
  
  primcorec path :: "'a \<Rightarrow> 'a inflist \<Rightarrow> bool" where
    "path u vs \<longleftrightarrow> R u (head vs) \<and> path (head vs) (tail vs)"
  
    
  primcorec path :: "'a \<Rightarrow> 'a inflist \<Rightarrow> bool" where
    "path u (InfCons v vs) \<longleftrightarrow> R u v \<and> path v vs"
*)  


end




(*
text \<open>We can use a coinductive list to represent paths. This definition is taken from the datypes documentation of Isabelle.\<close>
codatatype (lset: 'a) llist =
  lnull: LNil
| LCons (lhd: 'a) (ltl: "'a llist")
for
  map: lmap
  rel: llist_all2
  pred: llist_all
where
  "ltl LNil = LNil"

type_synonym 'v path = "'v llist" *)

text \<open>
  A strategy for player i is a function \<sigma>:V*Vi\<rightarrow>V that selects a successor for every history of the
  play ending in a vertex of player i.
  A strategy is memoryless iff \<sigma>(wv) = \<sigma>(v) for all w\<in>V*, v\<in>Vi.
  A strategy is winning from a vertex v if all plays starting in v and consistent with \<sigma> are winning
  for player i.
\<close>

locale arena = arena_defs E V\<^sub>0 
  for  
    E :: "'v dgraph"
  and V\<^sub>0 :: "'v set"  
  + 
  assumes V0_ss: "V\<^sub>0 \<subseteq> V"
  assumes succ: "E``{v}\<noteq>{}"
  assumes fin: "finite (UNIV::'v set)"
begin

text \<open>Wholly unnecessary but allows me to not have to unfold V1_def all the time.\<close>
lemma V1_ss[simp]: "V\<^sub>1 \<subseteq> V"
  unfolding V\<^sub>1_def
  by auto

definition connected where "connected v v' \<longleftrightarrow> (v,v')\<in>E\<^sup>*"
  
lemma conn: "v\<in>V \<Longrightarrow> connected v v' \<Longrightarrow> v'\<in>V"
  unfolding connected_def V_def
  by (metis Range.RangeI Range_snd UnCI rtranclE)

(* An attempt to translate the is_ipath from above into the context of the arena *)
coinductive is_play :: "'v \<Rightarrow> 'v inflist \<Rightarrow> bool" where
  "v \<in> succs E u \<Longrightarrow> is_play v vs \<Longrightarrow> is_play u (InfCons v vs)"

find_theorems is_play

lemma [simp]: "is_play u vs \<Longrightarrow> u\<in>V"
  using is_play.simps unfolding succs_def V_def
  by (metis Image_singleton_iff UnI1 fst_conv imageI)

lemma [simp]: "is_play u (InfCons v vs) \<Longrightarrow> v\<in>V"
  using is_play.simps unfolding succs_def V_def
  by (metis ImageE UnI2 imageI inflist.inject snd_conv)

(* Wouldn't it be nice to have a definition that shows whether any path is a valid play?  *)
coinductive is_play_2 :: "'v inflist \<Rightarrow> bool" where
  "v\<in>V \<Longrightarrow> (v,w) \<in> E \<Longrightarrow> is_play_2 (InfCons v (InfCons w vs))"

find_theorems is_play_2

(* These are just the same lemmas as above, translated for is_play_2 *)
lemma [simp]:"is_play_2 (InfCons v vs) \<Longrightarrow> v\<in>V"
  using is_play_2.simps unfolding V_def by blast

lemma [simp]:"is_play_2 (InfCons u (InfCons v vs)) \<Longrightarrow> v\<in>V"
  using is_play_2.simps unfolding V_def
  apply simp
  by (metis image_eqI snd_conv)

(* A play contains no dead ends. *)
lemma no_dead_ends[simp]:"is_play_2 vs \<Longrightarrow> \<forall>v\<in>infset vs. succs E v \<noteq> {}"
  using succ unfolding succs_def by auto

(* This one is very obvious but I'm just trying things here *)
lemma "is_play_2 (InfCons u (InfCons v vs)) \<Longrightarrow> (u,v)\<in>E"
  using is_play_2.simps by blast

(* Not sure if this is actually useful at all, and the proof is clearly a huge mess. *)
lemma "is_play_2 vs \<Longrightarrow> \<forall>v\<in>infset vs. v\<in>V"
  using is_play_2.simps unfolding V_def
  by (metis Image_singleton_iff Un_iff equals0I fst_conv imageI succ)
  

text \<open>
  A winning play for the even player is a play in which the highest priority that occurs
  infinitely often is even
\<close>

(*TO DO*)

text \<open>A positional strategy for a player i is a function \<sigma>:Vi\<rightarrow>V\<close>
type_synonym 'a strat = "'a \<Rightarrow> 'a"
(*A set of pairs might also work?*)

primcorec induced_play :: "'v \<Rightarrow> 'v strat \<Rightarrow> 'v inflist" where
  "induced_play v s = InfCons v (induced_play (s v) s)"

(*
  If a strategy always gives successors from E, then the induced play is a valid one.
  BUT: this also assumes the strategy gives moves for both players, which is not quite right.
*)
lemma "\<forall>v\<in>V. (s::'v strat) v\<in>V \<and> (v, s v)\<in>E \<Longrightarrow> u\<in>V \<Longrightarrow> is_play_2 (induced_play u s)"
  apply (coinduction)
  by (metis induced_play.ctr)
(*TO DO*)

end
  
end
