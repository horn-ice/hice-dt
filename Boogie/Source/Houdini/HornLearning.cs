using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie.Houdini
{

    /// <summary>
    /// This class represents a node of a decision tree.
    /// </summary>
    public class TreeNode
    {

        /// <summary>
        /// The attribute of the node (if it is a split node)
        /// </summary>
        public string attribute = null;

        /// <summary>
        /// The integer value at which to cut (if it is an integer split node)
        /// </summary>
        public int cut = 0;

        /// <summary>
        /// The label of the node (if it is a leaf node)
        /// </summary>
        public bool classification = false;

        /// <summary>
        /// The cildren of this node
        /// </summary>
        public TreeNode[] children = null;


        /// <summary>
        /// Creates an empty tree node.
        /// </summary>
        public TreeNode()
        {
        }


        /// <summary>
        /// Generates a Boogie expression equivalent to the decision tree rooted at this node.
        /// </summary>
        /// <param name="attr2Expr">A mapping that maps attribute names to their corresponding expressions</param>
        /// <returns>a Boogie expression equivalent to the decision tree rooted at this node.</returns>
        public Expr constructBoogieExpr(Dictionary<string, Expr> attr2Expr)
        {

            List<Expr> pathFromRoot = new List<Expr>();
            List<Expr> pathFormulas = new List<Expr>();

            constructBoogieExpr(this, pathFromRoot, attr2Expr, pathFormulas);

            Debug.Assert(pathFromRoot.Count == 0);

            return makeDisjunction(pathFormulas);

        }


        /// <summary>
        /// Generates a Boogie expression equivalent to the decision tree rooted at this node. This method assumes that the
        /// tree rooted at this node only contains integer splits.
        /// </summary>
        /// <param name="pathFromRoot">A list of expresseions that have been collected on the path from the root of the tree up to this node</param>
        /// <param name="attr2Expr">A mapping that maps attribute names to their corresponding expressions</param>
        /// <param name="pathFormulas">A list of conjunctions (one for each path from the root to a leaf labeled with true) that have been collected
        /// during the tree traversal thus far</param>
        private static void constructBoogieExpr(TreeNode node, List<Expr> pathFromRoot, Dictionary<string, Expr> attr2Expr, List<Expr> pathFormulas)
        {

            Debug.Assert(node != null);

            //
            // this node is a leaf, end of recursion
            //
            if (node.children == null)
            {

                // If node is labeled with True, add conjunction of expressions along the path
                if (node.classification)
                {
                    pathFormulas.Add(makeConjunction(pathFromRoot));
                }

            }


            //
            // This node is an inner node
            //
            else
            {

                Debug.Assert(attr2Expr.ContainsKey(node.attribute));

                Expr attrExpr = attr2Expr[node.attribute];

                //
                // Boolean attribute
                //
                if (attrExpr.ShallowType.IsBool)
                {

                    Debug.Assert(node.children != null && node.children.Length == 2 && node.children[0] != null && node.children[1] != null);
                    Debug.Assert(node.cut == 0);

                    // Get expression for decision predicate of the current node
                    Expr decisionPredicate = attr2Expr[node.attribute].Clone() as Expr;

                    // Make recusrive call for left child (test evaluates to true)
                    pathFromRoot.Add(Expr.Not(decisionPredicate));
                    constructBoogieExpr(node.children[0], pathFromRoot, attr2Expr, pathFormulas);
                    pathFromRoot.RemoveAt(pathFromRoot.Count - 1);

                    // Make recusrive call for right child (test evaluates to true)
                    pathFromRoot.Add(decisionPredicate);
                    constructBoogieExpr(node.children[1], pathFromRoot, attr2Expr, pathFormulas);
                    pathFromRoot.RemoveAt(pathFromRoot.Count - 1);

                }

                //
                // Integer attribute
                //
                else if (attrExpr.ShallowType.IsInt)
                {

                    Debug.Assert(node.children != null && node.children.Length == 2 && node.children[0] != null && node.children[1] != null);

                    // Get expression for decision predicate of the current node
                    Expr decisionPredicate = Expr.Le(attr2Expr[node.attribute].Clone() as Expr, Expr.Literal(node.cut));

                    // Make recusrive call for left child (test evaluates to true)
                    pathFromRoot.Add(decisionPredicate);
                    constructBoogieExpr(node.children[0], pathFromRoot, attr2Expr, pathFormulas);
                    pathFromRoot.RemoveAt(pathFromRoot.Count - 1);

                    // Make recusrive call for right child (test evaluates to true)
                    pathFromRoot.Add(Expr.Not(decisionPredicate));
                    constructBoogieExpr(node.children[1], pathFromRoot, attr2Expr, pathFormulas);
                    pathFromRoot.RemoveAt(pathFromRoot.Count - 1);

                }

                //
                // Unsopported attribute
                //
                else
                {
                    throw new MLHoudiniInternalError("While constructing a Boogie expression from JSON, encountered a unknown type of attribute");
                }

            }

        }


        /// <summary>
        /// Creates a disjunction of all given expressions.
        /// </summary>
        /// <param name="disjuncts">A (possibly empty) list of expressions</param>
        /// <returns>a disjunction of all given expressions</returns>
        public static Expr makeDisjunction(List<Expr> disjuncts)
        {

            // If null or empty list, return false
            if (disjuncts == null || disjuncts.Count == 0)
            {
                return Expr.False;
            }

            // Construct conjunction
            Expr e = disjuncts.First();
            for (int i = 1; i < disjuncts.Count; ++i)
            {
                e = Expr.Or(e, disjuncts[i]);
            }

            return e;

        }


        /// <summary>
        /// Creates a conjunction of all given expressions.
        /// </summary>
        /// <param name="conjuncts">A (possibly empty) list of expressions</param>
        /// <returns>a conjunction of all given expressions</returns>
        public static Expr makeConjunction(List<Expr> conjuncts)
        {

            // If null or empty list, return true
            if (conjuncts == null || conjuncts.Count == 0)
            {
                return Expr.True;
            }

            Expr e = conjuncts.First();
            for (int i = 1; i < conjuncts.Count; ++i)
            {
                e = Expr.And(e, conjuncts[i]);
            }

            return e;

        }


        /// <summary>
        /// Returns a string representation of the tree rooted at this node.
        /// </summary>
        /// <returns>a string representation of the tree rooted at this node</returns>
        public override string ToString()
        {
            return ToString(0);
        }


        /// <summary>
        /// Returns a string representation of the tree rooted at this node where the subtree rooted at this node
        /// is indented according to the parameter indent.
        /// </summary>
        /// <param name="indent">The number of spaces the subtree rooted at this node is indented</param>
        /// <returns>a string representation of the tree rooted at this node</returns>
        private string ToString(uint indent)
        {


            string str = "";

            for (uint i = 0; i < indent; ++i)
            {
                str += " ";
            }

            str += "attribute='" + attribute + "'; cut=" + cut + "; classification=" + classification;

            if (children == null)
            {
                str += ", children=null";
            }
            else
            {

                for (int i = 0; i < children.Length; ++i)
                {

                    if (children[i] == null)
                    {
                        str += Environment.NewLine + "null";
                    }
                    else
                    {
                        str += Environment.NewLine + children[i].ToString(indent + 4);
                    }

                }

            }

            return str;

        }

    }



    /// <summary>
    /// This class represents an implementation of an existential function.
    /// </summary>
    class DecisionTreeDomain : MLICEDomain
    {

        /// <summary>
        /// The names of the formal parameters of this function
        /// </summary>
        List<string> vars;

        /// <summary>
        /// The implementation of this function
        /// </summary>
        Expr model;


        /// <summary>
        /// Creates the implementation "true" with the given formal parameters.
        /// </summary>
        /// <param name="functionFormalParams">The formal parameters of the existential function</param>
        public DecisionTreeDomain(List<Variable> functionFormalParams)
        {

            // Store name of each formal parameter
            vars = new List<string>();
            foreach (var v in functionFormalParams)
            {
                vars.Add(v.Name);
            }

            // Initialize the invariant function with "true".
            model = Expr.True;
            
        }


        public bool constructModel(string funcName, TreeNode root, Dictionary<string, Dictionary<string, Expr>> attr2Expr, Dictionary<string, int> functionID)
        {

            Debug.Assert(attr2Expr.Keys.Contains(funcName));
            Debug.Assert(functionID.Keys.Contains(funcName));

            // We expect the root of the tree to be labaled with the categorical attribute splitting of the category of the exitential functions
            if (root.attribute != MLHoudini.attributeNameOfExistentialFunctions)
            {
                throw new MLHoudiniInternalError("Root node of decision tree must be a split on the existential functions");
            }


            return constructModel(root.children[functionID[funcName]], attr2Expr[funcName]);

        }



        /// <summary>
        /// Replaces the implementation of this existential function with the one given by the procided decision tree (without categorical split nodes)
        /// and returns whether the implmentation has changed.
        /// </summary>
        /// <param name="node">The root of a decision tree</param>
        /// <param name="attr2Expr">The mapping of attribute names to expressions</param>
        /// <returns>true if the implmentation has changed and false otherwise</returns>
        private bool constructModel(TreeNode node, Dictionary<string, Expr> attr2Expr)
        {

            // Remember old implementation
            Expr oldmodel = model;

            // Get new implementation
            if (node == null)
            {
                model = Expr.False;
            }
            else
            {
                model = node.constructBoogieExpr(attr2Expr);
            }
            

            return !ExtendsExpr.EqualityComparer(model, oldmodel);

        }


        /// <summary>
        /// Returns the implementation of the model where the formal parameters (the variables) are substituted with newvars.
        /// </summary>
        /// <param name="newvars">The variables used to replace the old variables with</param>
        /// <returns></returns>
        public Expr Gamma(List<Expr> newvars)
        {
            return ExtendsExpr.replace(model, vars, newvars);
        }

    }
}
