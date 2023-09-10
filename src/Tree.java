final public class Tree {

    /*@ nullable @*/ Tree left;
    /*@ nullable @*/ Tree right;

    int key;
    boolean isRed;

    // a variant decreasing from root to leafs used for recursive methods traversing the tree
    //@ ghost instance int heightVariant;

	
    /*@ normal_behaviour
        ensures \fresh(this);
        ensures this.key == key;
        ensures isRed == true;
        ensures left == null && right == null;
        ensures heightVariant == 1;
        ensures treeSet() == \dl_iSet_singleton(key);
        ensures validRBSubtree();
        ensures blackHeight(this) == 1;
        assignable this.key;
      @*/
    public Tree(int key) {
        this.key = key;
        isRed = true;
        //@ set heightVariant = 1;
    }

	
    /* -------------------------------------
     *           TREE STRUCTURE
     * -------------------------------------
     */

    /*@ model_behaviour 
        requires \invariant_for(this);
        accessible \set_minus(footprint(), \set_union(isRed, 
                                                      (left  == null ? \empty: \singleton(left.isRed)), 
                                                      (right == null ? \empty: \singleton(right.isRed)), 
                                                      heightVariant));
        measured_by heightVariant;
        helper model \locset footprint() {
        return \set_union( this.*,
               \set_union( left  == null ? \empty: left.footprint(), 
                           right == null ? \empty: right.footprint()));
        }
      @*/
  
    /*@ model_behaviour 
        requires \invariant_for(this);
        accessible \set_minus(footprint(), \set_union(isRed, 
                                                      (left  == null ? \empty: \singleton(left.isRed)), 
                                                      (right == null ? \empty: \singleton(right.isRed)), 
                                                      heightVariant));
        measured_by heightVariant;
        helper model \free treeSet() {
        return \dl_iSet_union( left  == null ? \dl_iSet_empty() : left.treeSet(),
               \dl_iSet_union( \dl_iSet_singleton(this.key),
                               right == null ? \dl_iSet_empty() : right.treeSet()));
        }
      @*/

      
    /* -------------------------------------
     *             INVARIANT
     * -------------------------------------
     */

    //          BINARY SEARCH TREE
    //--------------------------------------

    /*@ public instance invariant
               (left != right || left == null || right == null)
            && 0 < heightVariant
            && (left  == null || ( left.heightVariant < heightVariant 
                                && \disjoint(this.*, left.footprint())
                                && \invariant_for(left)))
            && (right == null || ( right.heightVariant < heightVariant
                                && \disjoint(this.*, right.footprint())
                                && \invariant_for(right)))
            && (\forall int k; invLessNotInRight(k))
            && (\forall int k; invGreaterNotInLeft(k))
            && (left == null || right == null || \disjoint(left.footprint(), right.footprint()));
        
        public instance accessible \inv: \set_minus(footprint(), \set_union(isRed, 
                                                      (left  == null ? \empty: \singleton(left.isRed)), 
                                                      (right == null ? \empty: \singleton(right.isRed))))
                        \measured_by heightVariant;
      @*/

    /*@ helper model boolean invLessNotInRight(int k) {
            return k < key ==> (right == null || !\dl_in(k, right.treeSet()));
        }
      @*/

    /*@ helper model boolean invGreaterNotInLeft(int k) {
            return k > key ==> (left == null || !\dl_in(k, left.treeSet()));
        }
      @*/

    /*@ helper model boolean invLessInTreeIffLeft(int k) {
            return k < key ==> (left == null || (\dl_in(k, treeSet()) <==> \dl_in(k, left.treeSet())));
        }
      @*/

    /*@ helper model boolean invGreaterInTreeIffRight(int k) {
            return k > key ==> (right == null || (\dl_in(k, treeSet()) <==> \dl_in(k, right.treeSet())));
        }
      @*/

    /*@ model_behaviour 
        requires (\forall int k; invLessNotInRight(k));
        ensures (\forall int k; invLessInTreeIffLeft(k));
        helper model boolean invLemmaLess() {
            return true;
        }
      @*/

    /*@ model_behaviour 
        requires (\forall int k; invGreaterNotInLeft(k));
        ensures (\forall int k; invGreaterInTreeIffRight(k));
        helper model boolean invLemmaGreater() {
            return true;
        }
      @*/

    
    //           RED BLACK TREE
    //--------------------------------------

    /*@ model_behaviour 
        requires \invariant_for(this);
        accessible \set_minus(footprint(), heightVariant);
        helper model boolean validRBSubtree() {
            return blackBalanced() && noDoubleRed();
        }
      @*/

    /*@ model_behaviour 
        requires \invariant_for(this);
        accessible \set_minus(footprint(), heightVariant);
        helper model boolean validRBSubtreeExceptRedTop() {
            return blackBalanced() 
                && (noDoubleRed() || doubleRedTop());
        }
      @*/

    //            BLACK HEIGHT
    //--------------------------------------

    /*@ model_behaviour 
        requires t == null || \invariant_for(t);
        accessible t == null ? \empty : \set_minus(t.footprint(), t.heightVariant);
        measured_by t == null ? 0 : t.heightVariant;
        helper model static int blackHeight(nullable Tree t) {
            return t == null ? 1
                : (t.isRed ? 0 : 1)
                    + (blackHeight(t.left) > blackHeight(t.right)
                    ? blackHeight(t.left)
                    : blackHeight(t.right));
        }
      @*/

    /*@ model_behaviour 
        requires \invariant_for(this);
        accessible \set_minus(footprint(), \set_union(isRed, heightVariant));
        measured_by heightVariant;
        helper model boolean blackBalanced() {
            return blackHeight(left) == blackHeight(right)
                && (left  != null ==> left.blackBalanced())
                && (right != null ==> right.blackBalanced());
        }
      @*/

    //             DOUBLE RED
    //--------------------------------------

    /*@ model_behaviour 
        requires \invariant_for(this);
        accessible \set_minus(footprint(), heightVariant);
        measured_by heightVariant;
        helper model boolean noDoubleRed() {
            return (left  != null ==> 
                    ((isRed ==> !left.isRed)  && left.noDoubleRed()))
                && (right != null ==> 
                    ((isRed ==> !right.isRed) && right.noDoubleRed()));
        }
      @*/

    /*@ model_behaviour 
        requires \invariant_for(this);
        accessible \set_minus(footprint(), heightVariant);
        helper model boolean doubleRedTop() {
            return doubleRedRight() || doubleRedLeft();
        }
      @*/

    /*@ model_behaviour 
        requires \invariant_for(this);
        accessible \set_minus(footprint(), heightVariant);
        helper model boolean doubleRedLeft() {
            return isRed 
                && left != null && left.isRed && left.noDoubleRed()
                && (right != null ==> 
                    (!right.isRed && right.noDoubleRed()));
        }
      @*/

    /*@ model_behaviour 
        requires \invariant_for(this);
        accessible \set_minus(footprint(), heightVariant);
        helper model boolean doubleRedRight() {
            return isRed 
                && right != null && right.isRed && right.noDoubleRed()
                && (left != null ==> 
                    (!left.isRed && left.noDoubleRed()));
        }
      @*/



    /* -------------------------------------
     *              CONTAINS
     * -------------------------------------
     */

    /*@ normal_behaviour
      @ requires true;
      @ ensures \dl_in(key, treeSet()) <==> \result == true;
      @ accessible footprint();
      @ assignable \strictly_nothing;
      @*/
    public boolean contains(int key) {
        Tree node = this;

        /*@ maintaining node == null ==> !\dl_in(key, treeSet());
          @ maintaining node != null ==> (\invariant_for(node) && (\dl_in(key, treeSet()) <==> \dl_in(key, node.treeSet())));
          @ decreasing node == null ? 0 : node.heightVariant;
          @ assignable \strictly_nothing;
          @*/
        while (node != null && node.key != key) {
            if (key < node.key) {
                //@ assert node.invLemmaLess();
                //@ assert node.invLessNotInRight(key) \by { auto classAxioms=false; }
                /*@ assert node.invLessInTreeIffLeft(key) \by {
                        rule Contract_axiom_for_invLemmaLess_in_Tree on="node_0.invLemmaLess()";
                        auto classAxioms=false steps=2000;
                    }
                  @*/
                node = node.left;

            } else {
                //@ assert node.invLemmaGreater();
                //@ assert node.invGreaterNotInLeft(key) \by { auto classAxioms=false; }
                /*@ assert node.invGreaterInTreeIffRight(key) \by {
                        rule Contract_axiom_for_invLemmaGreater_in_Tree on="node_0.invLemmaGreater()";
                        auto classAxioms=false steps=2000;
                    }
                  @*/
                node = node.right;

            }
        }

        return node != null;
    }



    /* -------------------------------------
     *                 ADD
     * -------------------------------------
     */

    /*@ normal_behaviour
      @ requires validRBSubtree();
      @ ensures validRBSubtreeExceptRedTop();
      @ ensures blackHeight(this) == \old(blackHeight(this));
      @ ensures isRed == \old(isRed)
      @         || (isRed && !isRed(left) && !isRed(right));
      @ ensures treeSet() == \dl_iSet_union(\old(treeSet()), \dl_iSet_singleton(key));
      @ ensures \new_elems_fresh(footprint());
      @ assignable footprint();
      @ measured_by heightVariant, 1;
      @*/
    public void add(int key) {
        
        if (key == this.key) {

            /*@ assert treeSet() == \dl_iSet_union(\old(treeSet()), \dl_iSet_singleton(key)) \by {
                    rule "setEq" on="(self.treeSet() = iSet_union(self.treeSet()@heapBefore_add, iSet_singleton(_key)))";
                    auto;
                }
              @*/
            return;

        } else if (key < this.key) {
            addLeft(key);
        } else {
            addRight(key);
        }

    }

    /*@ normal_behaviour
      @ requires key < this.key;
      @ requires validRBSubtree();
      @ ensures validRBSubtreeExceptRedTop();
      @ ensures blackHeight(this) == \old(blackHeight(this));
      @ ensures isRed == \old(isRed)
      @         || (isRed && !isRed(left) && !isRed(right));
      @ ensures treeSet() == \dl_iSet_union(\old(treeSet()), \dl_iSet_singleton(key));
      @ ensures \new_elems_fresh(footprint());
      @ assignable footprint();
      @ measured_by heightVariant, 0;
      @*/
    private void addLeft(int key) {
        
        if (this.left == null) {

            this.left = new Tree(key);
            //@ set heightVariant = heightVariant + 1;

        } else {

            this.left.add(key);
            setHeight();

            //          fix operations
            // ----------------------------------

            if (!isRed && left.isRed) {
                
                // recolouring if uncle is red -> potentially moves double red up the tree
                if (isRed(right) & (isRed(left.left) | isRed(left.right))) {
                    recolour();
                    return;
                }

                // rotations if uncle is black -> fixes double red completely
                // rotation to make double red "outer"
                if (isRed(left.right)) {
                    left.leftRotate();
                    setHeight();
                }
                // rotation to fix double red
                if (isRed(left.left)) {
                    rightRotate();
                }

            }
        }
    }

    /*@ normal_behaviour
      @ requires key > this.key;
      @ requires validRBSubtree();
      @ ensures validRBSubtreeExceptRedTop();
      @ ensures blackHeight(this) == \old(blackHeight(this));
      @ ensures isRed == \old(isRed)
      @         || (isRed && !isRed(left) && !isRed(right));
      @ ensures treeSet() == \dl_iSet_union(\old(treeSet()), \dl_iSet_singleton(key));
      @ ensures \new_elems_fresh(footprint());
      @ assignable footprint();
      @ measured_by heightVariant, 0;
      @*/
    private void addRight(int key) {

        //          add new leaf
        // ----------------------------------
        if (this.right == null) {
            
            Tree newRight = new Tree(key);
            this.right = newRight;

            //@ set heightVariant = heightVariant + 1;

            //@ assert left_eq:                 this.left == \old(this.left) \by { auto; }
            //@ assert left_inv:                \old(this.left) == null || \old(\invariant_for(this.left)) \by { auto classAxioms=false; }
            /*@ assert left_footprint:          this.left == null || this.left.footprint() == \old(this.left.footprint()) \by {
                    rule recall_left_eq;
                    oss;
                    rule applyEq on="self.left@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" occ=2;
                    dependency on="(self.left@heap).footprint()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                    expand on="self.<inv>";
                    auto classAxioms=false steps=5000;
                }
              @*/
            /*@ assert left_tree_set:           this.left == null || this.left.treeSet() == \old(this.left.treeSet()) \by {
                    rule recall_left_eq;
                    oss;
                    rule applyEq on="self.left@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" occ=2;
                    dependency on="(self.left@heap).treeSet()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                    auto classAxioms=false steps=5000;
                }
              @*/

            //@ assert right_eq:                right == newRight \by { auto; }
            /*@ assert inv:                     \invariant_for(this) \by {
                    expand on="self.<inv>";
                    oss;
                    assert "self.left@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant] = null
                            | (self.left.heightVariant@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant] < self.heightVariant@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]
                            & disjoint(self.*, self.left.footprint()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]))" \by {
                        auto classAxioms=false steps=5000;
                    }
                    assert "self.left@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant] = null
                            | self.left.<inv>@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" \by {
                        leave; // TODO: rule below does not work
                        // rule observerDependency on="self.left.<inv>@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                        // auto; 
                        // auto classAxioms=false steps=5000;
                    }
                    assert "disjoint(self.*, self.right.footprint()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant])" \by {
                        rule recall_right_eq;
                        oss;
                        rule applyEq on="self.right@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" occ=1;
                        expand on="self_0.footprint()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                        auto classAxioms=false;
                    }
                    assert "self.right.<inv>@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" \by {
                        auto steps=3000;
                    }
                    assert "self.left@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant] = null
                            | self.right@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant] = null
                            | disjoint(self.left.footprint()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant], self.right.footprint()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant])" \by {
                        rule recall_right_eq;
                        oss;
                        rule applyEq on="self.right@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" occ=4;
                        expand on="self_0.footprint()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                        auto classAxioms=false steps=2000;
                    }
                    assert "\forall int k_0; (inInt(k_0) -> self.invLessNotInRight(k_0)@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant] = TRUE)" \by {
                        // TODO(A): rule below does not work due to quantified variable -- try new 'formula' parameter
                        // expand on="self.invGreaterNotInLeft(k)@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" formula="\forall int k; (inInt(k) -> self.invGreaterNotInLeft(k)@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant] = TRUE)";
                        leave;
                    }
                    assert "\forall int k; (inInt(k) -> self.invGreaterNotInLeft(k)@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant] = TRUE)" \by {
                        leave;
                    }
                    expand on="self.<inv>@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                    auto steps=2000;
                }
              @*/
            /*@ assert tree_set:                treeSet() == \dl_iSet_union(\old(treeSet()), \dl_iSet_singleton(key)) \by {
                    oss;
                    rule "setEq" on="self.treeSet()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant] = iSet_union(self.treeSet(), iSet_singleton(key))";
                    expand on="self.treeSet()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                    expand on="self.treeSet()";
                    assert "self.right.treeSet()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant] 
                            = self_0.treeSet()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" \by auto;
                    expand on="self_0.treeSet()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                    auto classAxioms=false steps=2000;
                }
              @*/
            /*@ assert new_elems_fresh:         \new_elems_fresh(footprint()) \by {
                    oss;
                    expand on="self.footprint()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                    expand on="self.footprint()";
                    assert "self.right.footprint()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant] 
                            = self_0.footprint()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" \by auto;
                    expand on="self_0.footprint()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                    auto classAxioms=false steps=2000;
                }
              @*/

            /*@ assert right_black_height:      blackHeight(right) == 1 && \old(blackHeight(right) == 1) \by {
                    rule recall_right_eq;
                    oss;
                    rule applyEq on="self.right@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" occ=1;
                    expand on="Tree.blackHeight(self.right)";
                    // TODO: dependency rule throws exception
                    // dependency on="Tree::blackHeight(store(store(heapAfter_Tree, self, Tree::$right, self_0), self, Tree::$heightVariant, add(Z(1(#)), int::select(heap, self, Tree::$heightVariant))), self_0)";
                    // expand on="self_0.footprint()@heapAfter_Tree";
                    // auto classAxioms=false steps=2000;
                }
              @*/
            /*@ assert left_black_height:       blackHeight(left) == \old(blackHeight(left)) \by {
                    rule recall_left_eq;
                    oss;
                    rule applyEq on="self.left@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" occ=1;
                    expand on="self.<inv>";
                    cut "self.left = null";
                    { case "use":
                        auto steps=1000;
                    }
                    { case "show":
                        expand on="self.left.<inv>" occ=0;
                        dependency on="Tree::blackHeight(store(store(heapAfter_Tree, self, Tree::$right, self_0), self, Tree::$heightVariant, add(Z(1(#)), int::select(heap, self, Tree::$heightVariant))), Tree::select(heap, self, Tree::$left))";
                        auto classAxioms=false steps=3000;
                    }
                }
              @*/
            /*@ assert black_balanced:          blackBalanced() \by {
                    rule recall_left_eq;
                    oss;
                    expand on="self.blackBalanced()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                    expand on="self_0.validRBSubtree()@heapAfter_Tree";
                    expand on="self.validRBSubtree()";
                    expand on="self.blackBalanced()";
                    expand on="self.<inv>";
                    assert "self_0.blackBalanced()@heapAfter_Tree = self.right.blackBalanced()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" \by { auto steps=2000; }
                    cut "self.left = null";
                    { case "use":
                        auto steps=1000;                       
                    }
                    { case "show":
                        expand on="self.left.<inv>" occ=0;
                        rule applyEq on="self.left@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" occ=3;
                        leave;
                        // by hand: use dependency contract, split goals, close each automatically
                        // as everything on its own is found in a few hundred steps, but together not even in 50000 steps
                    }
                }
              @*/
            //@ assert black_height:            blackHeight(this) == \old(blackHeight(this)) \by { auto steps=2000; }

            /*@ assert left_double_red:         left == null || left.noDoubleRed() \by {
                    rule recall_left_eq;
                    auto steps=3;
                    rule applyEq on="self.left@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" occ=1;
                    rule applyEq on="self.left@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" occ=1;
                    expand on="self.validRBSubtree()";
                    expand on="self.noDoubleRed()";
                    rule unlimit_Tree_noDoubleRed on="Tree::noDoubleRed$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                    expand on="self.<inv>";
                    expand on="self.left.<inv>" occ=0;
                    dependency on="(self.left@heap).noDoubleRed()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                    auto classAxioms=false steps=8000;
                }
              @*/
            /*@ assert right_double_red:         right.noDoubleRed() \by {
                    rule recall_right_eq;
                    oss;
                    rule applyEq on="self.right@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]" occ=1;
                    expand on="self_0.validRBSubtree()@heapAfter_Tree";
                    auto steps=3000;
                }
              @*/

            /*@ assert validRBSubtreeExceptRedTop() \by {
                    oss;
                    expand on="self.validRBSubtreeExceptRedTop()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                    expand on="self.noDoubleRed()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                    expand on="self.doubleRedTop()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                    expand on="self.doubleRedRight()@heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant]";
                    expand on="self.validRBSubtree()";
                    expand on="self.noDoubleRed()";
                    auto classAxioms=false steps=1000;
                }
              @*/

            //@ assert colour:                  isRed == \old(isRed) \by { auto; }

            /*@ assert \dl_assignable(\old(\dl_heap()), \old(footprint())) \by {
                    oss;
                    rule assignableDefinition on="assignable(heapAfter_Tree[self.right := self_0][self.heightVariant := 1 + self.heightVariant], heap, self.footprint())";
                    expand on="self.footprint()" occ=0;
                    auto classAxioms=false steps=1000;
                }
            @*/



        //         add recursively
        // ----------------------------------
        } else {
            
            //@ assert right_inv:               \invariant_for(this.right) \by { auto classaxioms=false; }
            this.right.add(key);
            
            //@ assert right_eq:                this.right == \old(this.right)                                  \by { auto; }
            //@ assert left_eq:                 this.left == \old(this.left)                                    \by { auto; }
            //@ assert left_inv:                \old(this.left) == null || \old(\invariant_for(this.left))      \by { expand on="self.<inv>"; auto; }
            /*@ assert left_footprint:          this.left == null || this.left.footprint() == \old(this.left.footprint()) \by {
                    oss;
                    assert "self.left.footprint()@heapAfter_add = (self.left@heap).footprint()@heapAfter_add" \by auto;
                    dependency on="(self.left@heap).footprint()@heapAfter_add";

                    cut "self.left = null";
                    { case "use": auto; }
                    { case "show":
                        expand on="self.<inv>";
                        expand on="self.left.<inv>" occ=1;
                        auto classAxioms=false steps=5000;
                    }
                }
              @*/
            /*@ assert left_treeset:            this.left == null || this.left.treeSet() == \old(this.left.treeSet()) \by {
                    oss;
                    assert "self.left.treeSet()@heapAfter_add = (self.left@heap).treeSet()@heapAfter_add" \by auto;
                    dependency on="(self.left@heap).treeSet()@heapAfter_add";

                    cut "self.left = null";
                    { case "use": auto; }
                    { case "show":
                        expand on="self.<inv>";
                        expand on="self.left.<inv>" occ=1;
                        auto classAxioms=false steps=3000;
                    }
                }
              @*/

            /*@ assert tree_set:                treeSet() == \dl_iSet_union(\old(treeSet()), \dl_iSet_singleton(key)) \by {
                    oss;
                    rule "setEq" on="self.treeSet()@heapAfter_add = iSet_union(self.treeSet(), iSet_singleton(key))";
                    expand on="self.treeSet()@heapAfter_add";
                    expand on="self.treeSet()";
                    expand on="self.<inv>";

                    assert "self.right@heapAfter_add = self.right" \by auto;
                    rule "applyEq" on="self.right@heapAfter_add" occ=1;
                    rule "applyEq" on="self.right@heapAfter_add" occ=1;
                    rule "unlimit_Tree_treeSet" on="Tree::treeSet$lmtd(heapAfter_add, self.right@heap)"  occ=1;
                    rule "applyEqReverse" on="Tree::treeSet(heapAfter_add, self.right@heap)"
                          inst_s="iSet_union(self.right.treeSet(), iSet_singleton(key))"
                          occ=2;
                    auto classAxioms=false steps=2000;
                }
              @*/
            /*@ assert new_elems_fresh:         \new_elems_fresh(footprint()) \by {
                    rule recall_right_eq;
                    auto steps=2;
                    expand on="self.footprint()@heapAfter_add";
                    expand on="self.footprint()";
                    expand on="self.<inv>";
                    assert "freshLocs(heap) = freshLocs(heap[self.heightVariant := 1 + self.heightVariant])" \by auto;
                    auto classAxioms=false steps=4000;
                }
              @*/
            
            /*@ assert left_black_height:       blackHeight(left) == \old(blackHeight(left)) \by {
                    rule recall_left_eq;
                    oss;
                    rule applyEq on="self.left@heapAfter_add" occ=1;
                    cut "self.left = null";
                    { case "use":
                        expand on="Tree::blackHeight(heapAfter_add, Tree::select(heap, self, Tree::$left))";
                        expand on="Tree.blackHeight(self.left)";
                        auto;
                    }
                    { case "show":
                        dependency on="Tree::blackHeight(heapAfter_add, Tree::select(heap, self, Tree::$left))";
                        expand on="self.<inv>";
                        expand on="self.left.<inv>" occ=1;
                        auto classAxioms=false steps=2000;
                    }
                }
              @*/
            /*@ assert left_balanced:           left == null || left.blackBalanced() == \old(left.blackBalanced()) \by {
                    rule recall_left_eq;
                    oss;
                    rule applyEq on="self.left@heapAfter_add" occ=2;
                    dependency on="(self.left@heap).blackBalanced()@heapAfter_add";

                    cut "self.left = null";
                    { case "use": auto; }
                    { case "show":
                        expand on="self.<inv>";
                        expand on="self.left.<inv>" occ=1;
                        auto classAxioms=false steps=2000;
                    }
                }
              @*/
            /*@ assert black_balanced:          blackBalanced() \by {
                    oss;
                    expand on="self.blackBalanced()@heapAfter_add";
                    expand on="(self.right@heap).validRBSubtreeExceptRedTop()@heapAfter_add";
                    expand on="self.validRBSubtree()";
                    expand on="self.blackBalanced()";
                    auto classAxioms=false steps=1000;
                }
              @*/
            /*@ assert black_height:            blackHeight(this) == \old(blackHeight(this)) \by {
                    oss;
                    expand on="Tree::blackHeight(heapAfter_add, self)";
                    expand on="Tree.blackHeight(self)";
                    expand on="self.<inv>";
                    auto classAxioms=false steps=1000;
                }
              @*/

            
            /*@ assert (left != right || left == null || right == null)
                && (left==null || (\disjoint(this.*, left.footprint()) && \invariant_for(left)))
                && (right==null || (\disjoint(this.*, right.footprint()) && \invariant_for(right)))
                && (\forall int k; invLessNotInRight(k))
                && (\forall int k; invGreaterNotInLeft(k))
                && (left==null || right==null || \disjoint(left.footprint(), right.footprint()));
              @*/
            setHeight();

            
            /*@ assert left_double_red:         left == null || left.noDoubleRed() == \old(left.noDoubleRed()) \by {
                    oss;
                    assert "self.left@heapAfter_setHeight = self.left" \by auto;
                    rule applyEq on="self.left@heapAfter_setHeight" occ=2;

                    // does not work like this, as there are two possible dependency contracts to use, with heap and with heapAfter_add
                    dependency on="(self.left@heap).noDoubleRed()@heapAfter_setHeight"; // TODO: use the one with heap

                    cut "self.left = null";
                    { case "use": auto; }
                    { case "show":
                        expand on="self.<inv>";
                        expand on="self.left.<inv>" occ=1;
                        auto classAxioms=false steps=2000;
                    }
                }
              @*/


            //          fix operations
            // ----------------------------------

            if (!isRed & right.isRed) {

                // recolouring if uncle is red -> potentially moves double red up the tree
                if (isRed(left) & (isRed(right.left) | isRed(right.right))) {
                    recolour();
                    return;
                }

                // rotations if uncle is black -> fixes double red completely
                // rotation to make double red "outer"
                if (isRed(right.left)) {

                    //@ assert right.doubleRedLeft();
                    right.rightRotate();
                    /*@ assert (left != right || left == null || right == null)
                        && (left==null || (\disjoint(this.*, left.footprint()) && \invariant_for(left)))
                        && (right==null || (\disjoint(this.*, right.footprint()) && \invariant_for(right)))
                        && (\forall int k; invLessNotInRight(k))
                        && (\forall int k; invGreaterNotInLeft(k))
                        && (left==null || right==null || \disjoint(left.footprint(), right.footprint()));
                      @*/
                    setHeight();
                    //@ assert isRed(right.right);
                }
                // rotation to fix double red
                if (isRed(right.right)) {

                    //@ assert \invariant_for(this);
                    //@ assert !isRed && right.doubleRedRight() && (left == null || !left.isRed && left.noDoubleRed());
                    leftRotate();

                    /*@ assert isRed == \old(isRed) \by {
                            expand on="self.<inv>";
                            auto;
                        }
                    @*/
                    /*@ assert validRBSubtreeExceptRedTop() \by {
                            leave; // different depending on how we got here
                        }
                    @*/
                    /*@ assert \invariant_for(this) \by {
                            leave;
                        }
                    @*/
                    /*@ assert \dl_assignable(\old(\dl_heap()), \old(footprint())) \by {
                            auto steps=1;
                            rule assignableDefinition on="assignable(heapAfter_leftRotate, heap, self.footprint())";
                            expand on="self.footprint()" occ=0;
                            auto classAxioms=false steps=1000;
                        }
                    @*/

                    return;
                }

            }

            /*@ assert isRed == \old(isRed) \by {
                    expand on="self.<inv>";
                    auto;
                }
              @*/
            /*@ assert validRBSubtreeExceptRedTop() \by {
                    leave; // different depending on how we got here
                }
              @*/
            /*@ assert \invariant_for(this) \by {
                    auto;
                }
              @*/
            /*@ assert \dl_assignable(\old(\dl_heap()), \old(footprint())) \by {
                    auto steps=1;
                    rule assignableDefinition on="assignable(heapAfter_setHeight, heap, self.footprint())";
                    expand on="self.footprint()" occ=0;
                    auto classAxioms=false steps=1000;
                }
              @*/
        }
    }



    /* -------------------------------------
     *             ROTATIONS
     * -------------------------------------
     */

    /*@ normal_behaviour
      @ requires right != null;
      @ requires blackBalanced();
      @ requires !isRed && right.doubleRedRight() && (left == null || !left.isRed && left.noDoubleRed())
      @          || doubleRedRight();
      @ ensures footprint() == \old(footprint());
      @ ensures treeSet() == \old(treeSet());
      @ ensures heightVariant <= \old(heightVariant) + 1;
      @ ensures isRed == \old(isRed);
      @ ensures left != null && left.isRed == \old(right.isRed);
      @ ensures \old(!isRed && right.doubleRedRight() && (left == null || !left.isRed && left.noDoubleRed())) 
      @             ==> noDoubleRed();
      @ ensures \old(doubleRedRight()) ==> doubleRedLeft();
      @ ensures blackBalanced();
      @ ensures \old(blackHeight(this)) == blackHeight(this);
      @ assignable footprint();
      @*/
    private void leftRotate() {
        Tree r = right;
        Tree rr = right.right;
        Tree rl = right.left;
        Tree l = left;

        right = rr;
        left = r;
        left.right = rl;
        left.left = l;

        int t = key;
        key = left.key;
        left.key = t;

        //@ set left.heightVariant = heightVariant;
        //@ set heightVariant = heightVariant + 1;
    }

    /*@ normal_behaviour
      @ requires left != null;
      @ requires blackBalanced();
      @ requires !isRed && left.doubleRedLeft() && (right == null || !right.isRed && right.noDoubleRed())
      @          || doubleRedLeft();
      @ ensures footprint() == \old(footprint());
      @ ensures treeSet() == \old(treeSet());
      @ ensures heightVariant <= \old(heightVariant) + 1;
      @ ensures isRed == \old(isRed);
      @ ensures right != null && right.isRed == \old(left.isRed);
      @ ensures \old(!isRed && left.doubleRedLeft() && (right == null || !right.isRed && right.noDoubleRed())) 
      @             ==> noDoubleRed();
      @ ensures \old(doubleRedLeft()) ==> doubleRedRight();
      @ ensures blackBalanced();
      @ ensures \old(blackHeight(this)) == blackHeight(this);
      @ assignable footprint();
      @*/
    private void rightRotate() {
        Tree l = left;
        Tree ll = left.left;
        Tree lr = left.right;
        Tree r = right;

        left = ll;
        right = l;
        right.left = lr;
        right.right = r;

        int t = key;
        key = right.key;
        right.key = t;

        //@ set right.heightVariant = heightVariant;
        //@ set heightVariant = heightVariant + 1;

        //@ assert right == \old(left) \by { auto; } // for a prettier heap

        //@ assert height_variant:          heightVariant <= \old(heightVariant) + 1            \by { auto; }
        //@ assert is_red:                  isRed == \old(isRed)                                \by { auto; }
        //@ assert right_not_null:          right != null && right.isRed == \old(left.isRed)    \by { auto; }

        //@ assert left_eq:                 left == \old(left.left)                             \by { auto; }
        //@ assert right_eq:                right == \old(left)                                 \by { auto; }
        //@ assert right_left_eq:           right.left == \old(left.right)                      \by { auto; }
        //@ assert right_right_eq:          right.right == \old(right)                          \by { auto; }

        // ---------- footprint ------------
        /*@ assert left_footprint:          left == null || left.footprint() == \old(left.left.footprint()) \by {
                rule recall_left_eq;
                auto steps=2;
                rule applyEq on="self.left@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=2;
                dependency on="(self.left.left@heap).footprint()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.<inv>";
                expand on="self.left.footprint()" occ=0;
                rule unlimit_java_lang_Object__inv_ on="java.lang.Object::<inv>$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                expand on="self.left.<inv>";
                auto classAxioms=false steps=2000;
            }
          @*/
        /*@ assert right_left_footprint:    right.left == null || right.left.footprint() == \old(left.right.footprint()) \by {
                rule recall_right_left_eq;
                auto steps=2;
                rule applyEq on="self.right.left@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=2;
                dependency on="(self.left.right@heap).footprint()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.<inv>";
                expand on="self.left.footprint()" occ=0;
                rule unlimit_java_lang_Object__inv_ on="java.lang.Object::<inv>$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                expand on="self.left.<inv>";
                auto classAxioms=false steps=2000;
            }
          @*/
        /*@ assert right_right_footprint:   right.right == null || right.right.footprint() == \old(right.footprint()) \by {
                rule recall_right_right_eq;
                auto steps=2;
                rule applyEq on="self.right.right@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=2;
                dependency on="(self.right@heap).footprint()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.<inv>";
                expand on="self.left.footprint()" occ=1;
                auto classAxioms=false steps=2000;
            }
          @*/
        /*@ assert right_footprint:         right.footprint() 
                                         == \old( \set_union(\set_union(left.*, left.right == null ? \empty : left.right.footprint()), 
                                                            right == null ? \empty : right.footprint()) ) \by {
                rule recall_right_not_null;
                auto steps=4;
                expand on="self.right.footprint()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                auto classAxioms=false steps=2000;
            }
          @*/
        /*@ assert footprint:               footprint() == \old(footprint()) \by {
                auto steps=1;
                expand on="self.footprint()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.footprint()";
                rule unlimit_Tree_footprint on = "Tree::footprint$lmtd(heap,Tree::select(heap,self,Tree::$left))";
                expand on="self.left.footprint()";
                auto classAxioms=false steps=2000;
            }
          @*/

        // ----------- treeSet -------------
        /*@ assert left_tree_set:           left == null || left.treeSet() == \old(left.left.treeSet()) \by {
                rule recall_left_eq;
                auto steps=2;
                rule applyEq on="self.left@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=2;
                dependency on="(self.left.left@heap).treeSet()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.<inv>";
                expand on="self.left.footprint()" occ=0;
                rule unlimit_java_lang_Object__inv_ on="java.lang.Object::<inv>$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                expand on="self.left.<inv>";
                auto classAxioms=false steps=1000;
            }
          @*/
        /*@ assert right_left_tree_set:     right.left == null || right.left.treeSet() == \old(left.right.treeSet()) \by {
                rule recall_right_left_eq;
                auto steps=2;
                rule applyEq on="self.right.left@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=2;
                dependency on="(self.left.right@heap).treeSet()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.<inv>";
                expand on="self.left.footprint()" occ=0;
                rule unlimit_java_lang_Object__inv_ on="java.lang.Object::<inv>$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                expand on="self.left.<inv>";
                auto classAxioms=false steps=1000;
            }
          @*/
        /*@ assert right_right_tree_set:    right.right == null || right.right.treeSet() == \old(right.treeSet()) \by {
                rule recall_right_right_eq;
                auto steps=2;
                rule applyEq on="self.right.right@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=2;
                dependency on="(self.right@heap).treeSet()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.<inv>";
                expand on="self.left.footprint()" occ=1;
                auto classAxioms=false steps=1000;
            }
          @*/
        /*@ assert right_tree_set:          right.treeSet() 
                                         == \old( \dl_iSet_union(\dl_iSet_union(\dl_iSet_singleton(key), left.right == null ? \dl_iSet_empty() : left.right.treeSet()), 
                                                                right == null ? \dl_iSet_empty() : right.treeSet()) ) \by {
                rule recall_right_not_null;
                auto steps=4;
                rule setEq on="self.right.treeSet()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]= iSet_union(iSet_union(iSet_singleton(self.key),\if (self.left.right = null)\then (iSet_empty)\else (self.left.right.treeSet())),\if (self.right = null)  \then (iSet_empty)  \else (self.right.treeSet()))";
                expand on="self.right.treeSet()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                assert "self.key = self.right.key@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                        \by auto;
                auto classAxioms=false steps=1000;
            }
          @*/
        /*@ assert tree_set:                treeSet() == \old(treeSet()) \by {
                auto steps=1;
                rule setEq on="self.treeSet()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant] = self.treeSet()";
                expand on="self.treeSet()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.treeSet()";
                rule unlimit_Tree_treeSet on = "Tree::treeSet$lmtd(heap,Tree::select(heap,self,Tree::$left))";
                expand on="self.left.treeSet()";
                auto classAxioms=false steps=2000;
            }
          @*/

        // ------------ inv ----------------
        /*@ assert right_inv:               \invariant_for(right) \by {
                expand on="self.<inv>" occ=0;
                expand on="self.left.footprint()" occ=0;
                expand on="self.left.footprint()" occ=0;
                rule unlimit_java_lang_Object__inv_ on="java.lang.Object::<inv>$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                rule unlimit_java_lang_Object__inv_ on="java.lang.Object::<inv>$lmtd(heap, Tree::select(heap, self, Tree::$right))";
                expand on="self.left.<inv>";
                oss;
                assert "(self.left.right != self.right | self.left.right = null) | self.right = null" \by {
                    assert "self.right.footprint() != empty" \by {
                        assert "self.right != null" \by auto;
                        rule notLeft on="self.right != null";
                        expand on="self.right.footprint()" occ=0;
                        rule equalityToElementOf on="union(allFields(Tree::select(heap, self, Tree::$right)), union(\if (Tree::select(heap, Tree::select(heap, self, Tree::$right), Tree::$left) = null) \then (empty) \else (Tree::footprint$lmtd(heap, Tree::select(heap, Tree::select(heap, self, Tree::$right), Tree::$left))), \if (Tree::select(heap, Tree::select(heap, self, Tree::$right), Tree::$right) = null) \then (empty) \else (Tree::footprint$lmtd(heap, Tree::select(heap, Tree::select(heap, self, Tree::$right), Tree::$right))))) = empty";
                        auto classAxioms=false steps=1000;
                    }
                    auto classAxioms=false steps=1000;
                }
                assert "self.left.right = null | self.right.left.<inv>@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]" \by {
                    rule recall_right_left_eq;
                    oss;
                    rule applyEq on="self.right.left@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=1;
                    rule unlimit_java_lang_Object__inv_ on="java.lang.Object::<inv>$lmtd(heap, Tree::select(heap, Tree::select(heap, self, Tree::$left), Tree::$right))";
                    dependency on="(self.left.right@heap).<inv>@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                    auto classAxioms=false steps=1000;
                }
                assert "self.right = null | self.right.right.<inv>@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]" \by {
                    rule recall_right_right_eq;
                    oss;
                    rule applyEq on="self.right.right@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=1;
                    dependency on="(self.right@heap).<inv>@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                    auto classAxioms=false steps=1000;
                }
                assert "self.left.right = null | self.right.left.heightVariant@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]
                        < self.heightVariant" \by {
                    assert "self.left != self.left.right" \by auto classAxioms=false;
                    assert "self != self.left.right" \by auto classAxioms=false;
                    assert "self.left.right.heightVariant = self.right.left.heightVariant@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                        \by auto classAxioms=false;
                    auto classAxioms=false;
                }
                assert "\forall int k_0; self.right.invLessNotInRight(k_0)@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant] = TRUE" \by {
                    rule recall_right_right_tree_set;
                    oss;
                    rule allRight on="\forall int k_0; self.right.invLessNotInRight(k_0)@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant] = TRUE";
                    // expand on="self.right.invLessNotInRight(k_0_0)@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                    leave; // same problem as at TODO(A)
                }
                assert "\forall int k; self.right.invGreaterNotInLeft(k)@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant] = TRUE" \by {
                    leave;
                }
                assert "self.right@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant] != null" \by auto;
                auto steps=1;
                expand on="self.right.<inv>@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                auto classAxioms=false steps=5000;
            }
          @*/
        
        /*@ assert inv:                     \invariant_for(this) \by {
                expand on="self.<inv>";
                expand on="self.left.footprint()" occ=0;
                expand on="self.left.footprint()" occ=0;
                rule unlimit_java_lang_Object__inv_ on="java.lang.Object::<inv>$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                rule unlimit_java_lang_Object__inv_ on="java.lang.Object::<inv>$lmtd(heap, Tree::select(heap, self, Tree::$right))";
                expand on="self.left.<inv>";
                auto steps=2;
                assert "\forall int k_0; self.invLessNotInRight(k_0)@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant] = TRUE" \by {
                    leave;
                }
                assert "\forall int k; self.invGreaterNotInLeft(k)@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant] = TRUE" \by {
                    leave;
                }
                expand on="self.<inv>@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                auto classAxioms=false dependencies=true steps=20000;
            }
          @*/

        // ---------- double red -----------
        /*@ assert left_double_red:         left == null || left.noDoubleRed() == \old(left.left.noDoubleRed()) \by {
                rule recall_left_eq;
                auto steps=2;
                rule applyEq on="self.left@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=2;
                dependency on="(self.left.left@heap).noDoubleRed()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.<inv>" occ=0;
                expand on="self.left.footprint()" occ=0;
                rule unlimit_java_lang_Object__inv_ on="java.lang.Object::<inv>$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                expand on="self.left.<inv>";
                auto classAxioms=false steps=1000;
            }
          @*/
        /*@ assert right_left_double_red:   right.left == null || right.left.noDoubleRed() == \old(left.right.noDoubleRed()) \by {
                rule recall_right_left_eq;
                auto steps=2;
                rule applyEq on="self.right.left@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=2;
                dependency on="(self.left.right@heap).noDoubleRed()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.<inv>" occ=0;
                expand on="self.left.footprint()" occ=0;
                rule unlimit_java_lang_Object__inv_ on="java.lang.Object::<inv>$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                expand on="self.left.<inv>";
                auto classAxioms=false steps=1000;
            }
          @*/
        /*@ assert right_right_double_red:  right.right== null || right.right.noDoubleRed() == \old(right.noDoubleRed()) \by {
                rule recall_right_right_eq;
                auto steps=2;
                rule applyEq on="self.right.right@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=2;
                dependency on="(self.right@heap).noDoubleRed()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.<inv>" occ=0;
                expand on="self.left.footprint()" occ=1;
                auto classAxioms=false steps=1000;
            }
          @*/
        /*@ assert right_double_red:        right.noDoubleRed() \by {
                rule recall_right_not_null;
                auto steps=4;
                expand on="self.right.noDoubleRed()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                cut "self.doubleRedLeft() = TRUE";
                { case "use":
                    expand on="self.doubleRedLeft()" occ=4;
                    expand on="self.left.noDoubleRed()";
                    auto classAxioms=false steps=1000;
                }
                { case "show":
                    expand on="self.left.doubleRedLeft()";
                    auto classAxioms=false steps=1000;
                }
            }
          @*/

        /*@ assert no_double_red:           \old(!isRed && left.doubleRedLeft() && (right == null || !right.isRed && right.noDoubleRed())) 
                                                        ==> noDoubleRed() \by {
                auto steps=1;
                expand on="self.noDoubleRed()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.left.doubleRedLeft()" occ=0;
                auto classAxioms=false steps=1000;
            }
          @*/
        /*@ assert double_red:              \old(doubleRedLeft()) ==> doubleRedRight() \by {
                auto steps=1;
                expand on="self.doubleRedLeft()" occ=0;
                expand on="self.left.noDoubleRed()";
                expand on="self.doubleRedRight()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                auto classAxioms=false steps=1000;
            }
          @*/


        // --------- black height ----------
        /*@ assert right_is_red:            right.isRed && \old(left.isRed) \by {
                oss;
                expand on="self.doubleRedLeft()" occ=2;
                expand on="self.left.doubleRedLeft()" occ=0;
                auto classAxioms=false;
            }
          @*/
        /*@ assert old_black_heights_same:  \old(blackHeight(left.left) == blackHeight(left.right) && blackHeight(left.right) == blackHeight(right)) \by {
                auto steps=1;
                expand on="self.blackBalanced()" occ=0;
                rule unlimit_Tree_blackBalanced on="Tree::blackBalanced$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                expand on="self.left.blackBalanced()";
                expand on="Tree.blackHeight(self.left)";
                auto classAxioms=false steps=1000;
            }
          @*/
        /*@ assert left_black_height:       blackHeight(left) == \old(blackHeight(left.left)) \by {
                rule recall_left_eq;
                auto steps=2;
                rule applyEq on="self.left@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=1;
                expand on="self.<inv>";
                expand on="self.left.footprint()" occ=0;
                rule unlimit_java_lang_Object__inv_ on="java.lang.Object::<inv>$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                expand on="self.left.<inv>";
                cut "self.left.left = null";
                { case "use":
                    expand on="Tree::blackHeight(store(store(store(store(store(store(store(store(heap,self,Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$left)),self,Tree::$right,Tree::select(heap,self,Tree::$left)),Tree::select(heap,self,Tree::$left),Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$right)),Tree::select(heap,self,Tree::$left),Tree::$right,Tree::select(heap,self,Tree::$right)),self,Tree::$key,int::select(heap,Tree::select(heap,self,Tree::$left),Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$key,int::select(heap,self,Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$heightVariant,int::select(heap,self,Tree::$heightVariant)),self,Tree::$heightVariant,add(Z(1(#)),int::select(heap,self,Tree::$heightVariant))),Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$left))";
                    expand on="Tree.blackHeight(self.left.left)" occ=0;
                    auto classAxioms=false steps=1000;
                }
                { case "show":
                    dependency on="Tree::blackHeight(store(store(store(store(store(store(store(store(heap,self,Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$left)),self,Tree::$right,Tree::select(heap,self,Tree::$left)),Tree::select(heap,self,Tree::$left),Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$right)),Tree::select(heap,self,Tree::$left),Tree::$right,Tree::select(heap,self,Tree::$right)),self,Tree::$key,int::select(heap,Tree::select(heap,self,Tree::$left),Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$key,int::select(heap,self,Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$heightVariant,int::select(heap,self,Tree::$heightVariant)),self,Tree::$heightVariant,add(Z(1(#)),int::select(heap,self,Tree::$heightVariant))),Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$left))";
                    auto classAxioms=false steps=1000;
                }
            }
          @*/
        /*@ assert right_left_black_height: blackHeight(right.left) == \old(blackHeight(left.right)) \by {
                rule recall_right_left_eq;
                auto steps=2;
                rule applyEq on="self.right.left@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=1;
                expand on="self.<inv>";
                expand on="self.left.footprint()" occ=0;
                rule unlimit_java_lang_Object__inv_ on="java.lang.Object::<inv>$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                expand on="self.left.<inv>";
                cut "self.left.right = null";
                { case "use":
                    expand on="Tree::blackHeight(store(store(store(store(store(store(store(store(heap,self,Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$left)),self,Tree::$right,Tree::select(heap,self,Tree::$left)),Tree::select(heap,self,Tree::$left),Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$right)),Tree::select(heap,self,Tree::$left),Tree::$right,Tree::select(heap,self,Tree::$right)),self,Tree::$key,int::select(heap,Tree::select(heap,self,Tree::$left),Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$key,int::select(heap,self,Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$heightVariant,int::select(heap,self,Tree::$heightVariant)),self,Tree::$heightVariant,add(Z(1(#)),int::select(heap,self,Tree::$heightVariant))),Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$right))";
                    expand on="Tree.blackHeight(self.left.right)" occ=0;
                    auto classAxioms=false steps=1000;
                }
                { case "show":
                    dependency on="Tree::blackHeight(store(store(store(store(store(store(store(store(heap,self,Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$left)),self,Tree::$right,Tree::select(heap,self,Tree::$left)),Tree::select(heap,self,Tree::$left),Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$right)),Tree::select(heap,self,Tree::$left),Tree::$right,Tree::select(heap,self,Tree::$right)),self,Tree::$key,int::select(heap,Tree::select(heap,self,Tree::$left),Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$key,int::select(heap,self,Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$heightVariant,int::select(heap,self,Tree::$heightVariant)),self,Tree::$heightVariant,add(Z(1(#)),int::select(heap,self,Tree::$heightVariant))),Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$right))";
                    auto classAxioms=false steps=1000;
                }
            }
          @*/
        /*@ assert right_right_black_height: blackHeight(right.right) == \old(blackHeight(right)) \by {
                rule recall_right_right_eq;
                auto steps=2;
                rule applyEq on="self.right.right@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=1;
                expand on="self.<inv>";
                expand on="self.left.footprint()" occ=1;
                cut "self.right = null";
                { case "use":
                    expand on="Tree::blackHeight(store(store(store(store(store(store(store(store(heap,self,Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$left)),self,Tree::$right,Tree::select(heap,self,Tree::$left)),Tree::select(heap,self,Tree::$left),Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$right)),Tree::select(heap,self,Tree::$left),Tree::$right,Tree::select(heap,self,Tree::$right)),self,Tree::$key,int::select(heap,Tree::select(heap,self,Tree::$left),Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$key,int::select(heap,self,Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$heightVariant,int::select(heap,self,Tree::$heightVariant)),self,Tree::$heightVariant,add(Z(1(#)),int::select(heap,self,Tree::$heightVariant))),Tree::select(heap,self,Tree::$right))";
                    expand on="Tree.blackHeight(self.right)" occ=0;
                    auto classAxioms=false steps=1000;
                }
                { case "show":
                    dependency on="Tree::blackHeight(store(store(store(store(store(store(store(store(heap,self,Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$left)),self,Tree::$right,Tree::select(heap,self,Tree::$left)),Tree::select(heap,self,Tree::$left),Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$right)),Tree::select(heap,self,Tree::$left),Tree::$right,Tree::select(heap,self,Tree::$right)),self,Tree::$key,int::select(heap,Tree::select(heap,self,Tree::$left),Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$key,int::select(heap,self,Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$heightVariant,int::select(heap,self,Tree::$heightVariant)),self,Tree::$heightVariant,add(Z(1(#)),int::select(heap,self,Tree::$heightVariant))),Tree::select(heap,self,Tree::$right))";
                    auto classAxioms=false steps=1000;
                }
            }
          @*/
        /*@ assert new_black_heights_same:  blackHeight(left) == blackHeight(right.left) && blackHeight(right.left) == blackHeight(right.right) \by {
                auto classAxioms=false steps=1000;
            }
          @*/

        /*@ assert black_height:            \old(blackHeight(this)) == blackHeight(this) \by {
                auto steps=1;
                expand on="Tree.blackHeight(self)";
                expand on="Tree::blackHeight(store(store(store(store(store(store(store(store(heap,self,Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$left)),self,Tree::$right,Tree::select(heap,self,Tree::$left)),Tree::select(heap,self,Tree::$left),Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$right)),Tree::select(heap,self,Tree::$left),Tree::$right,Tree::select(heap,self,Tree::$right)),self,Tree::$key,int::select(heap,Tree::select(heap,self,Tree::$left),Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$key,int::select(heap,self,Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$heightVariant,int::select(heap,self,Tree::$heightVariant)),self,Tree::$heightVariant,add(Z(1(#)),int::select(heap,self,Tree::$heightVariant))),self)";
                rule unlimit_Tree_blackHeight_static_Tree on="Tree::blackHeight$lmtd(heap, Tree::select(heap, self, Tree::$left))"
                    occ=1;
                expand on="Tree.blackHeight(self.left)";
                rule unlimit_Tree_blackHeight_static_Tree on="Tree::blackHeight$lmtd(store(store(store(store(store(store(store(store(heap,self,Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$left)),self,Tree::$right,Tree::select(heap,self,Tree::$left)),Tree::select(heap,self,Tree::$left),Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$right)),Tree::select(heap,self,Tree::$left),Tree::$right,Tree::select(heap,self,Tree::$right)),self,Tree::$key,int::select(heap,Tree::select(heap,self,Tree::$left),Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$key,int::select(heap,self,Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$heightVariant,int::select(heap,self,Tree::$heightVariant)),self,Tree::$heightVariant,add(Z(1(#)),int::select(heap,self,Tree::$heightVariant))),Tree::select(store(store(store(store(store(store(store(store(heap,self,Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$left)),self,Tree::$right,Tree::select(heap,self,Tree::$left)),Tree::select(heap,self,Tree::$left),Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$right)),Tree::select(heap,self,Tree::$left),Tree::$right,Tree::select(heap,self,Tree::$right)),self,Tree::$key,int::select(heap,Tree::select(heap,self,Tree::$left),Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$key,int::select(heap,self,Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$heightVariant,int::select(heap,self,Tree::$heightVariant)),self,Tree::$heightVariant,add(Z(1(#)),int::select(heap,self,Tree::$heightVariant))),self,Tree::$right))"
                    occ=1;
                expand on="Tree::blackHeight(store(store(store(store(store(store(store(store(heap,self,Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$left)),self,Tree::$right,Tree::select(heap,self,Tree::$left)),Tree::select(heap,self,Tree::$left),Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$right)),Tree::select(heap,self,Tree::$left),Tree::$right,Tree::select(heap,self,Tree::$right)),self,Tree::$key,int::select(heap,Tree::select(heap,self,Tree::$left),Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$key,int::select(heap,self,Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$heightVariant,int::select(heap,self,Tree::$heightVariant)),self,Tree::$heightVariant,add(Z(1(#)),int::select(heap,self,Tree::$heightVariant))),Tree::select(store(store(store(store(store(store(store(store(heap,self,Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$left)),self,Tree::$right,Tree::select(heap,self,Tree::$left)),Tree::select(heap,self,Tree::$left),Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$right)),Tree::select(heap,self,Tree::$left),Tree::$right,Tree::select(heap,self,Tree::$right)),self,Tree::$key,int::select(heap,Tree::select(heap,self,Tree::$left),Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$key,int::select(heap,self,Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$heightVariant,int::select(heap,self,Tree::$heightVariant)),self,Tree::$heightVariant,add(Z(1(#)),int::select(heap,self,Tree::$heightVariant))),self,Tree::$right))";
                auto classAxioms=false steps=1000;
            }
          @*/

        /*@ assert left_balanced:           left == null || left.blackBalanced() == \old(left.left.blackBalanced()) \by {
                rule recall_left_eq;
                auto steps=2;
                rule applyEq on="self.left@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=2;
                dependency on="(self.left.left@heap).blackBalanced()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.<inv>";
                expand on="self.left.footprint()" occ=0;
                rule unlimit_java_lang_Object__inv_ on="java.lang.Object::<inv>$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                expand on="self.left.<inv>";
                auto classAxioms=false steps=2000;
            }
          @*/
        /*@ assert right_left_balanced:     right.left == null || right.left.blackBalanced() == \old(left.right.blackBalanced()) \by {
                rule recall_right_left_eq;
                auto steps=2;
                rule applyEq on="self.right.left@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=2;
                dependency on="(self.left.right@heap).blackBalanced()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.<inv>";
                expand on="self.left.footprint()" occ=0;
                rule unlimit_java_lang_Object__inv_ on="java.lang.Object::<inv>$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                expand on="self.left.<inv>";
                auto classAxioms=false steps=2000;
            }
          @*/
        /*@ assert right_right_balanced:    right.right== null || right.right.blackBalanced() == \old(right.blackBalanced()) \by {
                rule recall_right_right_eq;
                auto steps=2;
                rule applyEq on="self.right.right@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]"
                                occ=2;
                dependency on="(self.right@heap).blackBalanced()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.<inv>";
                expand on="self.left.footprint()" occ=1;
                auto classAxioms=false steps=2000;
            }
          @*/
        /*@ assert right_balanced:          right.blackBalanced() \by {
                rule recall_right_not_null;
                auto steps=4;
                expand on="self.right.blackBalanced()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="self.blackBalanced()" occ=0;
                rule unlimit_Tree_blackBalanced on="Tree::blackBalanced$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                expand on="self.left.blackBalanced()";
                auto classAxioms=false steps=1000;
            }
          @*/

        /*@ assert black_balanced:          blackBalanced() \by {
                auto steps=1;
                expand on="self.blackBalanced()@heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant]";
                expand on="Tree::blackHeight(store(store(store(store(store(store(store(store(heap,self,Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$left)),self,Tree::$right,Tree::select(heap,self,Tree::$left)),Tree::select(heap,self,Tree::$left),Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$right)),Tree::select(heap,self,Tree::$left),Tree::$right,Tree::select(heap,self,Tree::$right)),self,Tree::$key,int::select(heap,Tree::select(heap,self,Tree::$left),Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$key,int::select(heap,self,Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$heightVariant,int::select(heap,self,Tree::$heightVariant)),self,Tree::$heightVariant,add(Z(1(#)),int::select(heap,self,Tree::$heightVariant))),Tree::select(store(store(store(store(store(store(store(store(heap,self,Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$left)),self,Tree::$right,Tree::select(heap,self,Tree::$left)),Tree::select(heap,self,Tree::$left),Tree::$left,Tree::select(heap,Tree::select(heap,self,Tree::$left),Tree::$right)),Tree::select(heap,self,Tree::$left),Tree::$right,Tree::select(heap,self,Tree::$right)),self,Tree::$key,int::select(heap,Tree::select(heap,self,Tree::$left),Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$key,int::select(heap,self,Tree::$key)),Tree::select(heap,self,Tree::$left),Tree::$heightVariant,int::select(heap,self,Tree::$heightVariant)),self,Tree::$heightVariant,add(Z(1(#)),int::select(heap,self,Tree::$heightVariant))),self,Tree::$right))";
                expand on="self.blackBalanced()" occ=0;
                rule unlimit_Tree_blackBalanced on="Tree::blackBalanced$lmtd(heap, Tree::select(heap, self, Tree::$left))";
                expand on="self.left.blackBalanced()";
                auto classAxioms=false steps=1000;
            }
          @*/

        // ---------------------------------
        /*@ assert \dl_assignable(\old(\dl_heap()), \old(footprint())) \by {
                auto steps=1;
                rule assignableDefinition on="assignable(heap[self.left := self.left.left][self.right := self.left][self.left.left := self.left.right][self.left.right := self.right][self.key := self.left.key][self.left.key := self.key][self.left.heightVariant := self.heightVariant][self.heightVariant := 1 + self.heightVariant],heap,self.footprint())";
                expand on="self.footprint()" occ=0;
                rule unlimit_Tree_footprint on="Tree::footprint$lmtd(heap,Tree::select(heap,self,Tree::$left))";
                expand on="self.left.footprint()";
                auto;
            }
          @*/
        // by hand: close final Usage by assignableDefinition and then eqSym on last eq therein
    }




    /* -------------------------------------
     *            ADD UTILITIES
     * -------------------------------------
     */

    /*@ normal_behaviour
      @ ensures \result == (t != null && t.isRed);
      @ accessible t == null ? \empty : t.footprint();
      @ assignable \strictly_nothing;
      @*/
    private static boolean isRed(/*@ nullable @*/ Tree t) {
        return t != null && t.isRed;
    }

    /*@ normal_behaviour
      @ requires (left != right || left == null || right == null)
            && (left==null || (\disjoint(this.*, left.footprint()) && \invariant_for(left)))
            && (right==null || (\disjoint(this.*, right.footprint()) && \invariant_for(right)))
            && (\forall int k; invLessNotInRight(k))
            && (\forall int k; invGreaterNotInLeft(k))
            && (left==null || right==null || \disjoint(left.footprint(), right.footprint()));
      @ ensures heightVariant > 0;
      @ ensures left == null || heightVariant > left.heightVariant;
      @ ensures right == null || heightVariant > right.heightVariant;
      @ ensures \invariant_for(this);
      @ ensures footprint() == \old(footprint());
      @ ensures treeSet() == \old(treeSet());
      @ ensures blackHeight(this) == \old(blackHeight(this));
      @ ensures blackBalanced() == \old(blackBalanced());
      @ ensures left == null || left.noDoubleRed() == \old(left.noDoubleRed());
      @ ensures right == null || right.noDoubleRed() == \old(right.noDoubleRed());
      @ ensures noDoubleRed() == \old(noDoubleRed());
      @ ensures doubleRedTop() == \old(doubleRedTop());
      @ ensures left == null || left.validRBSubtreeExceptRedTop() == \old(left.validRBSubtreeExceptRedTop());
      @ ensures right == null || right.validRBSubtreeExceptRedTop() == \old(right.validRBSubtreeExceptRedTop());
      @ ensures validRBSubtreeExceptRedTop() == \old(validRBSubtreeExceptRedTop());
      @ ensures validRBSubtree() == \old(validRBSubtree());
      @ assignable heightVariant;
      @ helper
      @*/
    private void setHeight() {

        /*@ requires left==null || (\disjoint(this.*, left.footprint()) && \invariant_for(left));
          @ requires right==null || (\disjoint(this.*, right.footprint()) && \invariant_for(right));
          @ ensures heightVariant > 0;
          @ ensures left == null || heightVariant > left.heightVariant;
          @ ensures right == null || heightVariant > right.heightVariant;
          @ signals_only \nothing;
          @ assignable heightVariant;
          @*/
        {
            //@ ghost int leftHeight = left == null ? 0 : left.heightVariant;
            //@ ghost int rightHeight = right == null ? 0 : right.heightVariant;
            //@ set heightVariant = 1 + (leftHeight > rightHeight ? leftHeight : rightHeight);
        }

        //@ assert left  == null || left.footprint() == \old(left.footprint());
        //@ assert right == null || right.footprint() == \old(right.footprint());
        //@ assert left  == null || left.treeSet() == \old(left.treeSet());
        //@ assert right == null || right.treeSet() == \old(right.treeSet());
        //@ assert blackHeight(left)  == \old(blackHeight(left));
        //@ assert blackHeight(right) == \old(blackHeight(right));
        //@ assert left  == null || left.blackBalanced() == \old(left.blackBalanced());
        //@ assert right == null || right.blackBalanced() == \old(right.blackBalanced());
        //@ assert left  == null || left.noDoubleRed() == \old(left.noDoubleRed());
        //@ assert right == null || right.noDoubleRed() == \old(right.noDoubleRed());

        /*@ assert (left != right || left == null || right == null)
            && (left==null || (\disjoint(this.*, left.footprint()) && \invariant_for(left)))
            && (right==null || (\disjoint(this.*, right.footprint()) && \invariant_for(right)))
            && (\forall int k; invLessNotInRight(k))
            && (\forall int k; invGreaterNotInLeft(k))
            && (left==null || right==null || \disjoint(left.footprint(), right.footprint()));
          @*/

        //@ assert footprint() == \old(footprint());
        //@ assert treeSet() == \old(treeSet());
        //@ assert blackHeight(this) == \old(blackHeight(this));
        //@ assert blackBalanced() == \old(blackBalanced());
        //@ assert noDoubleRed() == \old(noDoubleRed());
        //@ assert doubleRedTop() == \old(doubleRedTop());
        //@ assert validRBSubtreeExceptRedTop() == \old(validRBSubtreeExceptRedTop());
        //@ assert validRBSubtree() == \old(validRBSubtree());
        //@ assert left == null || left.validRBSubtreeExceptRedTop() == \old(left.validRBSubtreeExceptRedTop());
        //@ assert right == null || right.validRBSubtreeExceptRedTop() == \old(right.validRBSubtreeExceptRedTop());
    }


    /*@ normal_behaviour
      @ requires right != null && left != null;
      @ requires left.validRBSubtreeExceptRedTop() && right.validRBSubtreeExceptRedTop();
      @ requires blackBalanced();
      @ requires !isRed && left.isRed && right.isRed &&
      @             (isRed(left.left) || isRed(left.right) || isRed(right.left) || isRed(right.right));
      @ ensures validRBSubtree();
      @ ensures isRed && !isRed(left) && !isRed(right);
      @ ensures blackHeight(this) == \old(blackHeight(this));
      @ ensures treeSet() == \old(treeSet());
      @ ensures footprint() == \old(footprint());
      @ assignable isRed, left.isRed, right.isRed;
      @*/
    private void recolour() {
        isRed = true;
        left.isRed = false;
        right.isRed = false;

        //@ assert left_eq:         left == \old(left)                  \by { auto; }
        //@ assert right_eq:        right == \old(right)                \by { auto; }
        //@ assert left_left_eq:    left.left == \old(left.left)        \by { auto; }
        //@ assert left_right_eq:   left.right == \old(left.right)      \by { auto; }
        //@ assert right_left_eq:   right.left == \old(right.left)      \by { auto; }
        //@ assert right_right_eq:  right.right == \old(right.right)    \by { auto; }

        //@ assert not_null:        right != null && left != null       \by { auto; }
        //@ assert isRed && !isRed(left) && !isRed(right);              // Evaluate Query for isRed's

        /*@ assert blackHeight(left.left) == \old(blackHeight(left.left)) \by {
                cut "self.left.left = null";
                { case "use":
                    expand on="Tree.blackHeight(self.left.left)";
                    expand on="Tree::blackHeight(heapBefore_recolour, Tree::select(heapBefore_recolour, Tree::select(heapBefore_recolour, self, Tree::$left), Tree::$left))";
                    auto classAxioms=false;
                }
                { case "show":
                    rule recall_left_left_eq;
                    oss;
                    rule applyEq on="self.left.left@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]" occ=1;
                    dependency on="Tree::blackHeight(store(store(store(heap, self, Tree::$isRed, TRUE), Tree::select(heap, self, Tree::$left), Tree::$isRed, FALSE), Tree::select(heap, self, Tree::$right), Tree::$isRed, FALSE), Tree::select(heap, Tree::select(heap, self, Tree::$left), Tree::$left))";
                    auto classAxioms=false;
                }
            }
          @*/
        /*@ assert blackHeight(left.right) == \old(blackHeight(left.right)) \by {
                cut "self.left.right = null";
                { case "use":
                    expand on="Tree.blackHeight(self.left.right)";
                    expand on="Tree::blackHeight(heapBefore_recolour, Tree::select(heapBefore_recolour, Tree::select(heapBefore_recolour, self, Tree::$left), Tree::$right))";
                    auto classAxioms=false;
                }
                { case "show":
                    rule recall_left_right_eq;
                    oss;
                    rule applyEq on="self.left.right@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]" occ=1;
                    dependency on="Tree::blackHeight(store(store(store(heap, self, Tree::$isRed, TRUE), Tree::select(heap, self, Tree::$left), Tree::$isRed, FALSE), Tree::select(heap, self, Tree::$right), Tree::$isRed, FALSE), Tree::select(heap, Tree::select(heap, self, Tree::$left), Tree::$right))";
                    auto classAxioms=false;
                }
            }
          @*/
        /*@ assert blackHeight(left) == \old(blackHeight(left)) + 1 \by {
                expand on="Tree.blackHeight(self.left)";
                expand on="Tree::blackHeight(heapBefore_recolour, Tree::select(heapBefore_recolour, self, Tree::$left))";
                auto classAxioms=false;
            }
          @*/
        /*@ assert blackHeight(right.left) == \old(blackHeight(right.left)) \by {
                cut "self.right.left = null";
                { case "use":
                    expand on="Tree.blackHeight(self.right.left)";
                    expand on="Tree::blackHeight(heapBefore_recolour, Tree::select(heapBefore_recolour, Tree::select(heapBefore_recolour, self, Tree::$right), Tree::$left))";
                    auto classAxioms=false;
                }
                { case "show":
                    rule recall_right_left_eq;
                    oss;
                    rule applyEq on="self.right.left@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]" occ=1;
                    dependency on="Tree::blackHeight(store(store(store(heap, self, Tree::$isRed, TRUE), Tree::select(heap, self, Tree::$left), Tree::$isRed, FALSE), Tree::select(heap, self, Tree::$right), Tree::$isRed, FALSE), Tree::select(heap, Tree::select(heap, self, Tree::$right), Tree::$left))";
                    auto classAxioms=false;
                }
            }
          @*/
        /*@ assert blackHeight(right.right) == \old(blackHeight(right.right)) \by {
                cut "self.right.right = null";
                { case "use":
                    expand on="Tree.blackHeight(self.right.right)";
                    expand on="Tree::blackHeight(heapBefore_recolour, Tree::select(heapBefore_recolour, Tree::select(heapBefore_recolour, self, Tree::$right), Tree::$right))";
                    auto classAxioms=false;
                }
                { case "show":
                    rule recall_right_right_eq;
                    oss;
                    rule applyEq on="self.right.right@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]" occ=1;
                    dependency on="Tree::blackHeight(store(store(store(heap, self, Tree::$isRed, TRUE), Tree::select(heap, self, Tree::$left), Tree::$isRed, FALSE), Tree::select(heap, self, Tree::$right), Tree::$isRed, FALSE), Tree::select(heap, Tree::select(heap, self, Tree::$right), Tree::$right))";
                    auto classAxioms=false;
                }
            }
          @*/
        /*@ assert blackHeight(right) == \old(blackHeight(right)) + 1 \by {
                expand on="Tree.blackHeight(self.right)";
                expand on="Tree::blackHeight(heapBefore_recolour, Tree::select(heapBefore_recolour, self, Tree::$right))";
                auto classAxioms=false;
            }
          @*/
        /*@ assert blackHeight(this) == \old(blackHeight(this)) \by {
                expand on="Tree.blackHeight(self)";
                expand on="Tree::blackHeight(heapBefore_recolour, self)";
                smt solver=Z3;
            }
          @*/

        /*@ assert left.blackBalanced() == \old(left.blackBalanced()) \by {
                rule recall_left_eq;
                oss;
                rule applyEq on="self.left@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]" occ=1;
                dependency on="(self.left@heap).blackBalanced()@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]";
                auto classAxioms=false;
            }
          @*/
        /*@ assert right.blackBalanced() == \old(right.blackBalanced()) \by {
                rule recall_right_eq;
                oss;
                rule applyEq on="self.right@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]" occ=1;
                dependency on="(self.right@heap).blackBalanced()@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]";
                auto classAxioms=false;
            }
          @*/
        /*@ assert blackBalanced() \by {
                auto steps=1;
                expand on="self.blackBalanced()@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]";
                expand on="self.blackBalanced()" occ=0;
                auto classAxioms=false;
            }
          @*/

        /*@ assert left.left == null || left.left.noDoubleRed() == \old(left.left.noDoubleRed()) \by {
                rule recall_left_left_eq;
                oss;
                rule applyEq on="self.left.left@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]" occ=2;
                dependency on="(self.left.left@heap).noDoubleRed()@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]";
                auto classAxioms=false;
            }
          @*/
        /*@ assert left.right == null || left.right.noDoubleRed() == \old(left.right.noDoubleRed()) \by {
                rule recall_left_right_eq;
                oss;
                rule applyEq on="self.left.right@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]" occ=2;
                dependency on="(self.left.right@heap).noDoubleRed()@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]";
                auto classAxioms=false;
            }
          @*/
        /*@ assert left.noDoubleRed() \by {
                rule recall_not_null;
                auto steps=5;
                expand on="self.left.noDoubleRed()@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]";
                auto steps=1;
                auto classAxioms=false proofSplitting=true proofSplisteps=3000;
            }
          @*/
        /*@ assert right.left == null || right.left.noDoubleRed() == \old(right.left.noDoubleRed()) \by {
                rule recall_right_left_eq;
                oss;
                rule applyEq on="self.right.left@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]" occ=2;
                dependency on="(self.right.left@heap).noDoubleRed()@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]";
                auto classAxioms=false;
            }
          @*/
        /*@ assert right.right == null || right.right.noDoubleRed() == \old(right.right.noDoubleRed()) \by {
                rule recall_right_right_eq;
                oss;
                rule applyEq on="self.right.right@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]" occ=2;
                dependency on="(self.right.right@heap).noDoubleRed()@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]";
                auto classAxioms=false;
            }
          @*/
        /*@ assert right.noDoubleRed() \by {
                rule recall_not_null;
                auto steps=5;
                expand on="self.right.noDoubleRed()@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]";
                auto steps=1;
                auto classAxioms=false proofSplitting=true steps=3000;
            }
          @*/
        /*@ assert noDoubleRed() \by {
                oss;
                expand on="self.noDoubleRed()@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]";
                auto classAxioms=false;
            }
          @*/

        /*@ assert validRBSubtree() \by {
                oss;
                expand on="self.validRBSubtree()@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]";
                auto classAxioms=false;
            }
          @*/

        /*@ assert treeSet() == \old(treeSet()) \by {
                oss;
                dependency on="self.treeSet()@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]";
                auto classAxioms=false;
            }
          @*/
        /*@ assert footprint() == \old(footprint()) \by {
                oss;
                dependency on="self.footprint()@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]";
                auto classAxioms=false;
            }
          @*/
        /*@ assert \invariant_for(this) \by {
                oss;
                dependency on="self.<inv>@heap[self.isRed := TRUE][self.left.isRed := FALSE][self.right.isRed := FALSE]";
                auto classAxioms=false;
            }
          @*/
    }
    
}
