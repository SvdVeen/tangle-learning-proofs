theory StrongConnectivity
  imports Main Digraphs
begin
(** A non-empty graph E with vertices V is strongly connected if for all pairs of vertices in the
    graph, there exists a path from one to the other and vice-versa.
    We do not have to specify the path from v' to v, as it follows from the definition. *)
definition strongly_connected :: "'v dgraph \<Rightarrow> 'v set \<Rightarrow> bool" where
  "strongly_connected E V \<equiv> E \<noteq> {} \<and>  E \<subseteq> V\<times>V \<and> (\<forall>v\<in>V. \<forall>v'\<in>V. (v,v')\<in>E\<^sup>*)"

(** An empty graph is not strongly connected. *)
lemma strongly_connected_notempty[simp]:
  "\<not>strongly_connected {} V"
  "\<not>strongly_connected E {}"
  unfolding strongly_connected_def by blast+

(** The edges in a strongly connected graph must include all vertices in V. *)
lemma strongly_connected_E_in_V: "strongly_connected E V \<Longrightarrow> E \<subseteq> V\<times>V"
  unfolding strongly_connected_def by blast

(** If a graph is strongly connected, there exists a path from every node to every other node. *)
lemma strongly_connected_path: "strongly_connected E V \<Longrightarrow> \<forall>v\<in>V. \<forall>v'\<in>V. \<exists>vs. path E v vs v'"
  unfolding strongly_connected_def
  using rtrancl_is_path[of _ _ E] by simp

context finite_graph_V_Succ
begin

(** A component in a graph is strongly connected when the graph restricted to that component is
    strongly connected and maximal; there is no single vertex outside of that component that can be
    added without breaking the strong connectivity. *)
definition SCC :: "'v set \<Rightarrow> bool" where
  "SCC R \<equiv> R \<subseteq> V \<and> strongly_connected (E\<inter>R\<times>R) (V\<inter>R) \<and>
   (\<forall>x\<in>V-R. let R'=insert x R in (\<not>strongly_connected(E\<inter>R'\<times>R') (V\<inter>R')))"

(** SCCs are non-empty because our strong connectivity definition excludes empty graphs. *)
lemma SCC_notempty[simp]: "\<not>SCC {}"
  unfolding SCC_def by fastforce

(** All strongly connected components are subsets of V. *)
lemma SCC_in_V: "SCC R \<Longrightarrow> R \<subseteq> V"
  unfolding SCC_def by simp

(** Strongly connected components are finite sets. *)
lemma SCC_finite: "SCC R \<Longrightarrow> finite R"
  using finite_subset[OF SCC_in_V fin_V] .

(** Trivial SCCs are excluded because we excluded non-empty graphs from the definition of strong
    connectivity.
    Our definition of SCCs checks strong connectivity of E restricted to the SCC. If the SCC is a
    single vertex without a self-edge, the restricted graph is empty by definition. *)
lemma SCC_nontrivial: "(v,v) \<notin> E \<Longrightarrow> \<not>SCC {v}"
  unfolding SCC_def by auto

(** A bottom SCC is a strongly connected component where there exist no edges from the SCC to the
    region outside of it; the SCC is closed. *)
definition bottom_SCC :: "'v set \<Rightarrow> bool" where
  "bottom_SCC R \<equiv> SCC R \<and> E `` R \<subseteq> R"

(** Bottom SCCs are strongly connected components. *)
lemma bottom_SCC_is_SCC: "bottom_SCC R \<Longrightarrow> SCC R"
  unfolding bottom_SCC_def by simp

(** Bottom SCCs are closed in E. *)
lemma bottom_SCC_closed: "bottom_SCC R \<Longrightarrow> E `` R \<subseteq> R"
  unfolding bottom_SCC_def by simp

(** Bottom SCCs are not empty because strongly connected components are not empty by our definition *)
lemma bottom_SCC_notempty[simp]: "\<not>bottom_SCC {}"
  using bottom_SCC_is_SCC by force

(** Bottom SCCs exist within the graph. *)
lemma bottom_SCC_in_V: "bottom_SCC R \<Longrightarrow> R \<subseteq> V"
  using bottom_SCC_is_SCC SCC_in_V by blast

(** Bottom SCCs are finite. *)
lemma bottom_SCC_finite: "bottom_SCC R \<Longrightarrow> finite R"
  using finite_subset[OF bottom_SCC_in_V fin_V] .

(** Bottom SCCs are not trivial (do not consist of a single node without a self loop) because SCCs
    are not trivial. *)
lemma bottom_SCC_nontrivial: "(v,v) \<notin> E \<Longrightarrow> \<not>bottom_SCC {v}"
  using bottom_SCC_is_SCC SCC_nontrivial by blast
end (** End of context finite_graph_V_Succ *)

end