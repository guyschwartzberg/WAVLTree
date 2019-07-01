/**
 *
 *
 * WAVLTree
 *
 * An implementation of a WAVL Tree.
 * (Haupler, Sen & Tarajan ‘15)
 *
 */

public class WAVLTree {
	private WAVLNode min; // a private field of the tree that points the minimum mode
	private WAVLNode max; // a private field of the tree that points the maximum mode
	private WAVLNode root; // a private field of the tree that points the root mode
	
	/**
	 * public WAVLTree()
	 * 
	 * a constructor of a new empty WAVL tree
	 */
	public WAVLTree()
	{
		root = new WAVLNode();
		this.min = root;
		this.max = root;
	}
	
	/**
	  * public boolean empty()
	  *
	  * returns true if and only if the tree is empty
	  *
	  */
	public boolean empty() 
	{
    return (!root.isInnerNode());
	}

	/**
	 * public String search(int k)
	 *
	 * returns the info of an item with key k if it exists in the tree
	 * otherwise, returns null
	 */
	public String search(int k)
	{
		if (k == min.key) return min.value;
		if (k == max.key) return max.value;
		WAVLNode found = rec_search(k, root);
		if (found == null)
			return null;
		return found.getValue();
	}
  
	private WAVLNode rec_search(int k, WAVLNode node)
  {
	  if(node.isInnerNode()){ // If not external
	        if(node.getKey() == k){
	           return node;
	        } else {
	        	WAVLNode foundNode = rec_search(k, node.getLeft());
	            if(foundNode == null) {
	                foundNode = rec_search(k, node.getRight());
	            }
	            return foundNode;
	         }
	    } else return null;
  }
  
  /**
   	* public int insert(int k, String i)
   *
   * inserts an item with key k and info i to the WAVL tree.
   * the tree must remain valid (keep its invariants).
   * returns the number of rebalancing operations, or 0 if no rebalancing operations were necessary.
   * returns -1 if an item with key k already exists in the tree.
   */
	public int insert(int k, String i) {
          int rebalanceCounter = 0;
          if (search(k) != null)
        	  return -1;
          if (root.rank == -1) { // insertion in case the tree is empty
        	  this.root = new WAVLNode(k, i);
        	  this.min = root;
        	  this.max = root;
          }
          else if (k < this.min.key) {  // insertion in case the new key is the minimum
        	  rebalanceCounter = insert(k, i, min);
        	  this.min = min.left;
          }
          else if (k > this.max.key) {  // insertion in case the new key is the maximum
        	  rebalanceCounter = insert(k, i, max);
        	  this.max = max.right;
          }
          else {  
        	  rebalanceCounter = insert(k, i, root);
          }
          return rebalanceCounter;
   }
   
	private int insert(int k, String i, WAVLNode cur) {
	   int insertBalanceCounter = 0;
	   if (k < cur.key) {
		   if (cur.left.rank != -1) { // recursively inserts to the left-subtree
			   insertBalanceCounter += insert(k ,i , cur.left);
		   }
		   else { // we've reached an insertion point and insert the new leaf 
			   WAVLNode newLeaf = new WAVLNode(k, i);
			   cur.left = newLeaf;
			   cur.left.parent = cur;
			   int tempRank = cur.rank;
			   cur.updateRank();
			   if (cur.rank != tempRank)
				   insertBalanceCounter++;
			   updateSubTreeSize(cur); // update sub-tree size for all parents
		   }
	   }
	   else if (k > cur.key) { // the symmetrical case with right-subtree 
		   if (cur.right.rank != -1) {
			   insertBalanceCounter += insert(k, i, cur.right);
		   }
		   else{ // we've reached an insertion point and insert the new leaf
			   WAVLNode newLeaf = new WAVLNode(k, i);
			   cur.right = newLeaf;
			   cur.right.parent = cur;
			   int tempRank = cur.rank;
			   cur.updateRank();
			   if (cur.rank != tempRank)
				   insertBalanceCounter++;
			   updateSubTreeSize(cur); // update sub-tree sizes to all parents 
		   }
	   } 
	   return balanceTree(cur) + insertBalanceCounter; //balancing the tree and returning the number of balancing operations
   }
   
   /**
    * private int balanceTree(WAVLNode cur)
    * 
    * balancing the tree after an insertion of new node
    * promoting the rank and rotating the nodes to get a balanced tree
    * 
    */
	private int balanceTree(WAVLNode cur) {
	   int rebalanceCounter = 0;
	   if (!cur.getLeft().isInnerNode() || !cur.getRight().isInnerNode()) {
		   while (cur.parent != null && ((cur.parent.rank - cur.rank == 0) && (cur.parent.rank - cur.getBrother().rank == 1))) { // CASE 1 Promote 
			   cur.parent.rank++;
			   cur = cur.getParent();
			   rebalanceCounter++;
		   }
		   // after we're done with the promotions, we get to the terminal operations :
		   // in case we've reached the root :
		   if (cur.parent == null) return rebalanceCounter; 
		   // in case we need to make rotations :
		   int balanceValue = balanceValue(cur.parent);  
		   if (balanceValue > 1 && cur.rank - cur.left.rank == 1 &&
				   cur.rank - cur.right.rank == 2) {  //left left rotation - CASE 1-2
			   rotate(1, cur.getBrother(), cur.getParent(), cur);
			   cur.getRight().updateRank();
			   rebalanceCounter += 2;
		   }
		   else if(balanceValue < -1 && cur.rank - cur.right.rank  == 1 &&
				   cur.rank - cur.left.rank == 2) { //right right rotation - CASE 2-1
			   rotate(0, cur.getBrother(), cur.getParent(), cur);
			   cur.getLeft().updateRank();
			   rebalanceCounter += 2;
		   }
		   else if(balanceValue > 1 && cur.rank - cur.left.rank == 2  &&
				   cur.rank - cur.right.rank == 1) {  //left right rotation - CASE 2-1
			   rotate(0, cur.getLeft(), cur, cur.getRight());
			   rotate(1, cur.getParent().getBrother(), cur.getParent().getParent(), cur.getParent());
			   cur.getBrother().updateRank();
			   cur.updateRank();
			   cur.getParent().updateRank();
			   rebalanceCounter += 5;
		   }
		   else if(balanceValue < -1 &&  cur.getRank() - cur.getRight().getRank() == 2  &&
				  cur.getRank() - cur.getLeft().getRank()== 1) { //right left rotation - CASE 1-2
			   rotate(1, cur.getRight(), cur, cur.getLeft());
			   rotate(0, cur.getParent().getBrother(), cur.getParent().getParent(), cur.getParent());
			   cur.getBrother().updateRank();
			   cur.updateRank();
			   cur.getParent().updateRank();
			   rebalanceCounter += 5;
		   }
	   }
	   return rebalanceCounter;
	   
   }
   
	   /**
    * private int balanceValue(WAVLNode cur)
    *
    * returns the difference between the rank of the node's children to know which rotation we should do  
    */
	private int balanceValue(WAVLNode cur) {
	   if (cur.rank==-1) return 0;
	   return (cur.left.rank - cur.right.rank);
   }

   /**
    * private void updateSubTreeSize(WAVLNode cur)
    * 
    * updates the subTreeSize of all the parents of a current node
    * after insertion to this node. 
    */
	private void updateSubTreeSize(WAVLNode cur){
	   while (cur != null){ // until we reached the root 
		   if (cur.rank != -1) 
			   cur.setSubtreeSize(cur.getLeft().getSubtreeSize() + cur.getRight().getSubtreeSize() + 1);
		   cur = cur.getParent();
		   
	   }
	}
	
   /**
    * public int delete(int k)
   *
   * deletes an item with key k from the binary tree, if it is there;
   * the tree must remain valid (keep its invariants).
   * returns the number of rebalancing operations, or 0 if no rebalancing operations were needed.
   * returns -1 if an item with key k was not found in the tree.
   */
	public int delete(int k)	 {
   	   int rebalancing_counter = 0;
       WAVLNode selected = rec_search(k,root); // finding the node we want to delete
       if (selected == null)
    	   return -1;
       if (min.equals(selected))
    	   min = successor(selected);
       if (max.equals(selected))
    	   max = predecessor(selected);
       WAVLNode substitute = remove_from_tree(selected); //finds the substitute node 
       Boolean tree_rebalanced = false; // rebalancing starts here 
       WAVLNode cur = substitute;
       WAVLNode parent = cur.parent;
       if (parent == null) { //if we delete the root
    	   if (cur.isInnerNode()) { 
    		   cur.updateRank();
    		   rebalancing_counter++;
    	   }
    	   return rebalancing_counter;
       }
       while (!tree_rebalanced) {
    	   if (cur.equals(root)) 
    		   return rebalancing_counter;
    	   WAVLNode brother = cur.getBrother();
           int balancing_factor_cur_parent = parent.getRank() - cur.getRank();
           int balancing_factor_bro_parent = parent.getRank() - brother.getRank();
           int orientation = 0; // For symmetry reasons
    	   if (cur.getParent().getLeft().equals(brother))
    		   orientation = 1;
    	   if (parent.isLeaf() && parent.getRank() == 1) {  // CASE LEAF
    		   parent.rank = parent.rank - 1;
    		   cur = parent;
    		   parent = parent.parent;
    		   brother = cur.getBrother();
    		   rebalancing_counter++;
    	   }
    	   else if (balancing_factor_cur_parent == 3) {
        	   if (balancing_factor_bro_parent	== 2){  // CASE 1
        		   parent.rank = parent.rank - 1;
        		   cur = parent;
        		   parent = parent.parent;
        		   rebalancing_counter++;
        		   if (parent == null)
        			   return rebalancing_counter;
        		   brother = cur.getBrother();
        	   }
        	   else if (balancing_factor_bro_parent == 1){ // CASE 2
        		   int balancing_factor_bro_left_child = brother.getRank() - brother.getLeft().getRank();
        		   int balancing_factor_bro_right_child = brother.getRank() - brother.getRight().getRank();
        		   if (balancing_factor_bro_left_child == 2 && balancing_factor_bro_right_child == 2){ // CASE 2
        			   parent.rank = parent.rank - 1;
        			   brother.rank = brother.rank - 1;
            		   cur = parent;
            		   parent = parent.parent;
            		   rebalancing_counter += 2;
            		   if (parent != null) 
            			   brother = parent.getBrother();
        		   }
        		   else if (orientation == 0) { // CASE 3&4 : LEFT TO RIGHT
        			   if ((balancing_factor_bro_left_child == 1 || balancing_factor_bro_left_child == 2) 
        					   && balancing_factor_bro_right_child == 1){ // CASE 3
        				   rotate(0, cur, parent, brother);
        				   tree_rebalanced = true; 
        				   rebalancing_counter += 3;
        				   parent.updateRank();
        				   brother.updateRank();
        				   parent.updateRank();
        			   }
        			   else if (balancing_factor_bro_left_child == 1
        					   && balancing_factor_bro_right_child == 2){ // CASE 4
        				   rotate(1, brother.getRight(), brother, brother.getLeft());
        				   rotate(0, cur, parent, cur.getBrother());
        				   parent.rank = parent.rank - 2;
        				   brother.updateRank();
        				   parent.getParent().rank = parent.getParent().rank + 2;
        				   tree_rebalanced = true;
        				   rebalancing_counter += 5;
        			   }
        		   }
        		   else {  // CASE 3&4 : RIGHT TO LEFT
        			   if ((balancing_factor_bro_right_child == 1 || balancing_factor_bro_right_child == 2) 
        					   && balancing_factor_bro_left_child == 1) { // CASE 3
        				   rotate(1, cur, parent, brother);
	    				   rebalancing_counter += 3;
	    				   tree_rebalanced = true; 
	    				   parent.updateRank();
	    				   brother.updateRank();
	    				   parent.updateRank();
        			   }
        			   else if (balancing_factor_bro_right_child == 1
        					   && balancing_factor_bro_left_child == 2){  // CASE 4 
        				   rotate(0, brother.getLeft(), brother, brother.getRight());
	    				   rotate(1, cur, parent, cur.getBrother());
	    				   parent.rank = parent.rank - 2;
	    				   brother.updateRank();
	    				   parent.getParent().rank = parent.getParent().rank + 2;
	    				   rebalancing_counter += 5;
	    				   tree_rebalanced = true; 
        			   }
        		   } 
        	   }		   
    	   } 
    	   else  tree_rebalanced = true;
    	   if (cur != null && cur.isInnerNode())
    		   cur.sub_tree_size = cur.getLeft().getSubtreeSize() + cur.getRight().getSubtreeSize() + 1;
    	   if (brother != null && brother.isInnerNode())
        	   brother.sub_tree_size = brother.getRight().getSubtreeSize() + brother.getLeft().getSubtreeSize() + 1;
    	   if (parent != null && parent.isInnerNode())
    		   parent.sub_tree_size = parent.getLeft().getSubtreeSize() + parent.getRight().getSubtreeSize() + 1;
       }
       return rebalancing_counter;
   }
   
   /**
    * private WAVLNode remove_from_tree(WAVLNode selected)
    * 
    * finds the substitute node of selected in the tree, deletes it and update the substitute's pointers
    */
	private WAVLNode remove_from_tree(WAVLNode selected){
	   WAVLNode substitute;
	   if (selected.isLeaf())  
		   substitute = new WAVLNode(); // if the node we delete is a leaf
       else if ((selected.getLeft().isInnerNode() && !selected.getRight().isInnerNode())) // if the node we delete is left-unary node
    	   substitute = selected.getLeft();
       else if ((selected.getRight().isInnerNode() && !selected.getLeft().isInnerNode())) // if the node we delete is right-unary node
    	   substitute = selected.getRight();
       else { // if the node we delete is inner non-unary node
    	   WAVLNode successor = successor(selected);
    	   WAVLNode next;
    	   if (successor != null && successor.isInnerNode()){
    		   next = remove_from_tree(successor);
    		   substitute = successor;
    	   }
    	   else {
    		   WAVLNode predecessor = predecessor(selected);
    		   next = remove_from_tree(predecessor); // removes the substitute node from our tree
    		   substitute = predecessor;
    	   }
    	   replace(selected, substitute); //replace and update the substitute's pointers
    	   substitute.setRight(selected.getRight());
    	   substitute.getRight().setParent(substitute);
    	   substitute.setLeft(selected.getLeft());
    	   substitute.getLeft().setParent(substitute);
    	   substitute.rank = selected.getRank();
    	   substitute.setSubtreeSize(selected.getSubtreeSize());
    	   return next; 
       }
	   replace(selected, substitute);
	   updateSubTreeSize(substitute);
	   return substitute;
   }
   
   /**
    * private void rotate(int orientation, WAVLNode cur, WAVLNode parent, WAVLNode brother)
    * 
    * making a rotation in the tree, given the orientation (left/right/left-right/right-left) and the nodes we'de like to rotate
    */
	private void rotate(int orientation, WAVLNode cur, WAVLNode parent, WAVLNode brother){
	   WAVLNode grandparent = parent.getParent();
	   if (orientation == 0) {
		   WAVLNode bro_left = brother.getLeft();
		   WAVLNode bro_right = brother.getRight();
		   if (bro_left == null)
			   bro_left = new WAVLNode();
		   if (bro_right == null)
			   bro_right = new WAVLNode();
		   parent.setRight(bro_left);
		   parent.getRight().setParent(parent);
		   brother.setLeft(parent);
		   brother.getLeft().setParent(brother);
		   brother.setRight(bro_right);
		   bro_right.setParent(brother);
	   }
	   else {
		   WAVLNode bro_left = brother.getLeft();
		   WAVLNode bro_right = brother.getRight();
		   if (bro_left == null)
			   bro_left = new WAVLNode();
		   if (bro_right == null)
			   bro_right = new WAVLNode();
		   parent.setLeft(bro_right);
		   parent.getLeft().setParent(parent);
		   brother.setRight(parent);
		   brother.getRight().setParent(brother);
		   brother.setLeft(bro_left);
		   bro_left.setParent(brother);
	   }
	   if (grandparent != null){
		   if (grandparent.getRight().equals(parent))
			   grandparent.setRight(brother);
		   else
			   grandparent.setLeft(brother);
	   }
	   else
	   {
		   root = brother;
	   }
	   brother.setParent(grandparent);	   
	   parent.setSubtreeSize(parent.getLeft().getSubtreeSize() + parent.getRight().getSubtreeSize() + 1);
	   brother.setSubtreeSize(brother.getLeft().getSubtreeSize() + brother.getRight().getSubtreeSize() + 1);
	   
		   
   }
   
   /**
    * private void replace(WAVLNode selected, WAVLNode substitute)
    * 
    * updates the pointers of the substitute node to be the ones of the selected node so id would replace it
    */
	private void replace(WAVLNode selected, WAVLNode substitute){
	   
	   if (!selected.equals(root)){
		   WAVLNode selected_parent = selected.getParent();
		   if (selected_parent.getLeft() == selected)
			   selected.parent.setLeft(substitute);
		   else
			   selected_parent.setRight(substitute);
		   substitute.setParent(selected_parent);
	   }
	   else 
	   {
		   if (!substitute.equals(selected.getLeft()))
		   {
			   substitute.setLeft(selected.getLeft());
			   substitute.getLeft().setParent(substitute);
		   }
		   if (!substitute.equals(selected.getRight()))
		   {
			   substitute.setRight(selected.getRight());
			   substitute.getRight().setParent(substitute);
		   }
		   substitute.setParent(null);
		   this.root = substitute;
	   }
	   
	   
	   
   }

   /**
    * public String min()
    *
    * Returns the info of the item with the smallest key in the tree,
    * or null if the tree is empty
    */
	public String min()  {
           return min.getValue();
   }

   /**
    * public String max()
    *
    * Returns the info of the item with the largest key in the tree,
    * or null if the tree is empty
    */
	public String max() {
           return max.getValue(); 
   }

   /**
    * public int[] keysToArray()
   *
   * Returns a sorted array which contains all keys in the tree,
   * or an empty array if the tree is empty.
   */
	public int[] keysToArray() {
	   int size = root.getSubtreeSize();
	   int [] keysArray = new int[size]; // create a new array of the tree size
	   WAVLNode node = min;
	   for (int i = 0; i < size; i++)  {
		   keysArray[i] = node.getKey();
		   node = successor(node); // add the elements to the array in increasing order
	   }
	   return keysArray;  
   }

   /**
    * public String[] infoToArray()
   *
   * Returns an array which contains all info in the tree,
   * sorted by their respective keys,
   * or an empty array if the tree is empty.
   */
	public String[] infoToArray()
   {
	   int size = root.getSubtreeSize();
	   String [] keysArray = new String[size]; // create a new array of the tree size
	   WAVLNode node = min;
	   for (int i = 0; i < size; i++) {
		   keysArray[i] = node.getValue();
		   node = successor(node); // add the value of the element to the array in increasing order
	   }
	   return keysArray; 
   }

   /**
    * public int size()
    *
    * Returns the number of nodes in the tree.
    *
    */
	public int size() {
	   	   if (root == null) return 0;
           return root.getSubtreeSize(); 
   }
   
     /**
    * public WAVLNode getRoot()
    *
    * Returns the root WAVL node, or null if the tree is empty
    *
    */
	public WAVLNode getRoot() {
       if (empty()) return null;   
	   return root;
   }
   
     /**
    * public int select(int i)
    *
    * Returns the value of the i'th smallest key (return -1 if tree is empty)
    * Example 1: select(1) returns the value of the node with minimal key 
    * Example 2: select(size()) returns the value of the node with maximal key 
    * Example 3: select(2) returns the value 2nd smallest minimal node, i.e the value of the node minimal node's successor  
    *
    */   
	public String select(int i) {
		return recSelect(i, root);
	}
	
	private String recSelect(int i, WAVLNode cur) {
	   	if (i > root.sub_tree_size || i <= 0 || this.empty()) // the index is out of bounds
	   		return "-1";
		if (cur.isLeaf())
			return cur.value;
	   	int leftSize = cur.left.sub_tree_size;
		if (i == leftSize + 1) // case A - i is the root index
			return cur.value;
		else if (i < leftSize + 1) // case B - i is smaller then the root index, then we recSelect in the sub-left tree
			return recSelect(i, cur.left);
		else 								// case C - i is greater then the root index, then we recSelect in the sub-right tree
			return recSelect(i-leftSize-1, cur.right);   
   }
   
   /**
    * private WAVLNode successor (WAVLNode n)
    * 
    * returns the successor of the WAVLNode n
    * 
    */
	private WAVLNode successor(WAVLNode n) {
	   if (max.equals(n) || root == null | root.getSubtreeSize() <= 1 || !n.isInnerNode())
		   return new WAVLNode();
	   if (n.getRight().isInnerNode())
		   return n.getRight().getMin(); //if n has right child, we go right to the end
	   WAVLNode cur = n.getParent();
	   while (cur != null && cur.isInnerNode() && n.equals(cur.getRight())) { // if not, go up to the successor
		   n = cur;
		   cur = n.getParent();
	   }
	   return cur; 
   }
   
   /**
    * private WAVLNode predecessor (WAVLNode n)
    * 
    * returns the predecessor of the WAVLNode n
    */
	private WAVLNode predecessor(WAVLNode n) {
	   if (min.equals(n) || root == null ||  root.getSubtreeSize() <= 1)
		   return new WAVLNode();
	   if (n.getLeft().isInnerNode())
		   return n.getLeft().getMax(); //if n has left child, we go left to the end
	   WAVLNode cur = n.getParent();
	   while (cur != null && cur.isInnerNode() && n.equals(cur.getLeft())) { // if not, go up to the successor
		   n = cur;
		   cur = n.getParent();
	   }
	   return cur;
   }
   
	/**
	* public class WAVLNode
  	*/
	public class WAVLNode{
	  
		  private int rank;
		  private int key;
		  private String value;
		  private WAVLNode parent;
		  private WAVLNode left;
		  private WAVLNode right;
		  private int sub_tree_size;
		  
	  /**
		   * public WAVLNode(int key, String value)
		   * 
		   * a constructor of a new WAVLNode with key k and info value
		   * the node has no children (his children are external nodes) and it has null parent 
		   * the rank is initialized to 0 and the size to 1
		   */
		  public WAVLNode(int key, String value) {
			  this.rank = 0;
			  this.key = key;
			  this.value = value;
			  this.parent = null;
			  this.left = new WAVLNode();
			  left.setParent(this);
			  this.right = new WAVLNode();
			  right.setParent(this);
			  sub_tree_size = 1;
		  }
		  
		  /**
		   * public WAVLNode()
		   * 
		   * a constructor of a new external WAVLNode
		   * the node has null children and null parent 
		   * it's rank is -1 and the size to 0
		   */
		  public WAVLNode(){
			  this.key = -1;
			  this.value = null;
			  this.parent = null;
			  this.left = null;
			  this.right = null;
			  this.rank = -1;
			  this.sub_tree_size = 0;
		  }
	
		  /**
		   * public int getKey()
		   * 
		   * returns the key of the node 
		   */
		  public int getKey() {
	            return key;
		  }
		  
		  /**
		   * public WAVLNode getParent()
		   * returns the parent of the node
		   */
		  public WAVLNode getParent() {
	            return parent; 
		  }
		  
		  /**
		   * public String getValue()
		   * 
		   * returns the value of the node
		   */
		  public String getValue() {
	            return value; 
		  }
		  
		  /**
		   * public int getRank() 
		   * 
		   * returns the rank of the node
		   */
		  public int getRank(){
	           return rank; 
		  }
		  
		  /**
		   *  public WAVLNode getLeft()
		   *  
		   * returns the left child of the node
		   */
		  public WAVLNode getLeft() {
	            return left; 
		  }
		  
		  /**
		   *  public WAVLNode getRight()
		   *  
		   * returns the right child of the node
		   */
		  public WAVLNode getRight() {
	            return right;
		  }
		  
		  /**
		   * public boolean isInnerNode()
		   * 
		   * return true if the node is inner node and false if external
		   */
		  public boolean isInnerNode() {
            return rank != -1; 
	  }

	  /**
	   		* public boolean isLeaf()
	   * 
	   * returns true if the node is a leaf or false otherwise 
	   */
		  public boolean isLeaf(){
	  		return (left.rank == -1 && right.rank == -1);
	  	}

	  	/**
	  	 	* public int getSubtreeSize()
	  	 * 
	  	 * returns the size of the sub tree with the node as a root
	  	 * 
	  	 */
		  public int getSubtreeSize(){
            return sub_tree_size; 
	  	}
   
	  	/**
	  	 	* public void setSubtreeSize(int newSize)
	  	 * 
	  	 * sets a new subTree size to the node
	  	 */
		  public void setSubtreeSize(int newSize) {
	  		this.sub_tree_size = newSize;
	  	}
    
	  	/**
	  	 	* public void setLeft(WAVLNode n)
	  	 * 
	  	 * set new left child for the node
	  	 */
		  public void setLeft(WAVLNode n){
	  		this.left = n;
	  	}
    
	  	/**
	  	 	* public void setRight(WAVLNode n)
	  	 * 
	  	 * set new right child for the node
	  	 */
		  public void setRight(WAVLNode n) {
	  		this.right = n;
	  	}
    
	  	/**
	  	 	* public void setParent(WAVLNode n)
	  	 * 
	  	 * set new parent for the node
	  	 */
		  public void setParent(WAVLNode n) {
	  		this.parent = n;
	  	}
    
	  	/**
	  	 * private WAVLNode getMin()
	  	 * 
	  	 * returns the min node in the subtree of the current node
	  	 */
		  private WAVLNode getMin(){
	  		WAVLNode n = this;
	  		while (n.getLeft().isInnerNode())
	  			n = n.getLeft();
	  		return n;
		  }	

		  /**
		   * private WAVLNode getMax()
		   * 
		   * returns the max node in the subtree of the current node
		   */
		  private WAVLNode getMax(){
			  WAVLNode n = this;
			  while (n.getRight().isInnerNode())
				  n = n.getRight();
			  return n;	
		  }
    
		  /**
		   * private WAVLNode getBrother()
		   * 
		   * returns the other child of this.parent 
		   */
		  private WAVLNode getBrother(){
			  if (parent == null)	
				  return null;
			  if (this.equals(parent.left))
				  return parent.getRight();
			  else
				  return parent.getLeft();
		  }

		  /**
		   * private void updateRank()
		   * 
		   * updates the rank of the current node based on the rank of it's children
		   */
		  private void updateRank(){
			  if (this.rank - left.rank == 3 && this.rank - right.rank == 3)
				  this.rank = this.rank - 1;
			  else
				  this.rank = Math.max(left.rank, right.rank) + 1;
		  }
	}
}