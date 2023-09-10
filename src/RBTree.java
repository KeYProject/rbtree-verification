final public class RBTree {
    
    /*@ nullable @*/ Tree root;

    /*@ model_behaviour 
        requires validRBTree();
        accessible footprint();
        helper model \locset footprint() {
            return \set_union(this.*, (root == null) ? \empty : root.footprint());
        }
      @*/
  
    /*@ model_behaviour 
        requires validRBTree();
        accessible footprint();
        helper model \free treeSet() {
            return (root == null) ? \dl_iSet_empty() : root.treeSet();
        }
      @*/


    /*@ model_behaviour
        requires \invariant_for(root);
        accessible footprint();
        helper model boolean validRBTree() {
            return root == null || (
                   \disjoint(this.*, root.footprint())
                && \invariant_for(root) 
                && root.validRBSubtree() 
                && !root.isRed
            );
        }
      @*/



    /*@ public normal_behaviour
      @ ensures validRBTree();
      @ ensures treeSet() == \dl_iSet_empty();
      @ ensures \fresh(footprint());
      @*/
    public RBTree() {
        // default constructor only made explicit for specification purposes
    }

    /*@ normal_behaviour
      @ requires validRBTree();
      @ ensures validRBTree();
      @ ensures \dl_in(key, treeSet()) <==> \result == true;
      @ accessible footprint();
      @ assignable \strictly_nothing;
      @*/
    public boolean contains(int key) {
        return root != null && root.contains(key);
    }

    /*@ normal_behaviour
      @ requires validRBTree();
      @ ensures validRBTree();
      @ ensures treeSet() == \dl_iSet_union(\old(treeSet()), \dl_iSet_singleton(key));
      @ ensures \new_elems_fresh(footprint());
      @ assignable footprint();
      @*/
    public void add(int key) {
        if (root == null) {
            root = new Tree(key);
        } else {
            root.add(key);
            //@ assert root == \old(root);
        }

        fixRootColour();
    }

    /*@ normal_behaviour
      @ requires root != null;
      @ requires \disjoint(this.*, root.footprint());
      @ requires \invariant_for(root);
      @ requires root.validRBSubtreeExceptRedTop();
      @ ensures validRBTree();
      @ ensures treeSet() == \old(treeSet());
      @ ensures footprint() == \old(footprint());
      @ assignable root.isRed;
      @*/
    private void fixRootColour() {
        root.isRed = false;
    }
}
