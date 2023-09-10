public class Client {

    /*@ normal_behaviour
      @ requires true;
      @ ensures true;
      @*/
    public static void main(String[] args) {

        RBTree t = new RBTree();

        /*
            -3      -3             5              5
                      \           / \            / \
                ~>     5   ~>   -3   9    ~>   -3   9
                                                   /       
                                                  7
        */
        t.add(-3);
        t.add(5);
        t.add(9);   // rotation
        t.add(7);   // recolouring
        
        //@ assert (\forall int k; t.contains(k) <==> (k == -3 || k == 5 || k == 9 || k == 7));
        //@ assert t.validRBTree();

    }



    public static void printTree(RBTree t) {
        System.out.println(treeString(t.root));
    }

    public static String treeString(Tree t) {
        return (t.left == null ? "" : ("(" + treeString(t.left) + ")-"))
            + t.key + (t.isRed ? "r" : "b")
            + (t.right == null ? "" : ("-(" + treeString(t.right) + ")"));
    }

}
