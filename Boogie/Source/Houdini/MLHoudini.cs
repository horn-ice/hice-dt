#define C5


using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using VC;
using Outcome = VC.VCGen.Outcome;
using Bpl = Microsoft.Boogie;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.GraphUtil;
//using Microsoft.Z3;
using Microsoft.Basetypes;
using Newtonsoft.Json;

namespace Microsoft.Boogie.Houdini {


    public static class ExtendsExpr
    {
        public static Expr replace(Expr expr, List<string> oldvars, List<Expr> newvars)
        {
            if (expr is LiteralExpr)
            {               
                LiteralExpr literalExpr = expr as LiteralExpr;
                return (literalExpr.Clone() as Expr);
            }
            else if (expr is IdentifierExpr)
            {
                IdentifierExpr identExpr = expr as IdentifierExpr;
                Debug.Assert(identExpr != null);
                int index = oldvars.IndexOf(identExpr.Name);
                Debug.Assert(index >= 0 && index < newvars.Count());
                Expr newExpr = newvars.ElementAt(index);                            
                return (newExpr.Clone() as Expr);
            }
            else if (expr is NAryExpr)
            {
                NAryExpr naryExpr = expr as NAryExpr;
                List<Expr> newargs = new List<Expr>();
                foreach (var exprarg in naryExpr.Args)
                {
                    newargs.Add(replace(exprarg, oldvars, newvars));                    
                }
                return new NAryExpr(Token.NoToken, naryExpr.Fun, newargs);
            }

            throw new MLHoudiniInternalError("Error: learned invariant is an expression of unexpected type!");
        }

        public static Expr conjunction(List<Expr> exprs)
        {
            if (exprs.Count() == 0)
            {
                return Expr.False;
            }
            else if (exprs.Count() == 1)
            {
                return exprs.ElementAt(0);
            }
            else
            {
                Expr lhs = exprs.ElementAt(0);
                exprs.RemoveAt(0);
                Expr rhs = conjunction(exprs);
                return Expr.And(lhs, rhs);
            }
        }

        /*
         * Assume that the argument has atleast one list of exprs in it.
         */
        public static Expr disjunction(List<List<Expr>> exprs)
        {
            Debug.Assert(exprs.Count() > 0);
            if (exprs.Count() == 1)
            {
                return conjunction(exprs.ElementAt(0));
            }
            else
            {
                Expr lhs = conjunction(exprs.ElementAt(0));
                exprs.RemoveAt(0);
                Expr rhs = disjunction(exprs);
                return Expr.Or(lhs, rhs);
            }            
        }

        public static bool EqualityComparer(Expr model, Expr newmodel)
        {
            /*
            if (model is LiteralExpr && newmodel is LiteralExpr)
            {
                LiteralExpr litmodel = model as LiteralExpr;
                LiteralExpr litnewmodel = newmodel as LiteralExpr;
                if (litnewmodel.Val.GetType() == typeof(bool) && litmodel.Val.GetType() == typeof(bool))
                {
                    return litnewmodel.Val == litmodel.Val;
                }
                else if (litnewmodel.Val.GetType() == typeof(BigNum) && litmodel.Val.GetType() == typeof(BigNum))
                {
                    return litnewmodel.Val.Equals(litmodel);
                }
                else if (litnewmodel.Val.GetType() == typeof(BigDec) && litmodel.Val.GetType() == typeof(BigDec))
                {
                    litnewmodel.Val.
                }


                return (literalExpr.Clone() as Expr);
            }
            else if (model is IdentifierExpr && newmodel is IdentifierExpr)
            {
                IdentifierExpr identExpr = expr as IdentifierExpr;
                Debug.Assert(identExpr != null);
                int index = oldvars.IndexOf(identExpr.Name);
                Debug.Assert(index >= 0 && index < newvars.Count());
                Expr newExpr = newvars.ElementAt(index);
                return (newExpr.Clone() as Expr);
            }
            else if (expr is NAryExpr)
            {
                NAryExpr naryExpr = expr as NAryExpr;
                List<Expr> newargs = new List<Expr>();
                foreach (var exprarg in naryExpr.Args)
                {
                    newargs.Add(replace(exprarg, oldvars, newvars));
                }
                return new NAryExpr(Token.NoToken, naryExpr.Fun, newargs);
            }*/
            return model.ToString() == newmodel.ToString();            
        }
    }

    public class dataPoint
    {
        public List<int> value;
        public string functionName;
        
        public dataPoint(string funcName, List<Model.Element> lm)
        {
            try
            {
                List<int> ret = new List<int>();
                foreach (var m in lm)
                {
                    if (m.Kind == Model.ElementKind.Boolean)
                    {
                        bool val = (m as Model.Boolean).Value;
                        if (val)
                        {
                            ret.Add(1);
                        }
                        else
                        {
                            ret.Add(0);
                        }
                    }
                    else if (m.Kind == Model.ElementKind.DataValue)
                    {
                        Model.DatatypeValue dv = (m as Model.DatatypeValue);
                        Debug.Assert(dv != null);
                        Debug.Assert(dv.Arguments.Count() == 1);
                        Model.Element arg = dv.Arguments[0];
                        Debug.Assert(arg.Kind == Model.ElementKind.Integer);
                        if (dv.ConstructorName.Equals("-"))
                        {
                            ret.Add(-1 * arg.AsInt());
                        }
                        else if (dv.ConstructorName.Equals("+"))
                        {
                            ret.Add(arg.AsInt());
                        }
                        else
                        {
                            throw new MLHoudiniInternalError("Unexpected constructor name in the data value returned by the model\n");
                        }
                    }
                    else
                    {
                        Debug.Assert(m.Kind == Model.ElementKind.Integer);
                        ret.Add(m.AsInt());
                    }
                }
                value = ret;
                functionName = funcName;
            }
            catch(Exception e)
            {
                Console.WriteLine("Exception caught while converting model into a list of integer");
                throw e;
            }
        }

        public override int GetHashCode()
        {
                if (this.value != null && this.functionName != null)
                    return this.value.Count + 100 * this.functionName.GetHashCode();
                else return 0;
        }

        public override bool Equals(object obj)
        {
                dataPoint other = obj as dataPoint;
                if (other == null)
                    return false;
                return this.value.SequenceEqual(other.value) && this.functionName.Equals(other.functionName);
        }

        public string print()
        {
            string ret = this.functionName + ":";
            if(value.Count() == 0)
            {
                ret += "empty";
            }
            else
            {
                ret += value[0].ToString();
            }
            for(int i = 1; i < value.Count(); i++)
            {
                ret += "," + value[i].ToString();
            }
            return ret;
        }

        public override string ToString()
        {
            return print();
        }


    }

    public class MLHoudini
    {
        Dictionary<string, Function> existentialFunctions;
        Program program;
        Dictionary<string, Implementation> name2Impl;
        Dictionary<string, VCExpr> impl2VC;
        Dictionary<string, List<Tuple<string, Function, NAryExpr>>> impl2FuncCalls;
        // constant -> the naryexpr that it replaced
        Dictionary<string, NAryExpr> constant2FuncCall;

        // function -> its abstract value
        Dictionary<string, MLICEDomain> function2Value;

        public const string attrPrefix = "$";
        public const string pcAttrName = "$pc";

        // impl -> functions assumed/asserted
        Dictionary<string, HashSet<string>> impl2functionsAsserted, impl2functionsAssumed;

        // funtions -> impls where assumed/asserted
        Dictionary<string, HashSet<string>> function2implAssumed, function2implAsserted;

        // impl -> handler, collector
        Dictionary<string, Tuple<ProverInterface.ErrorHandler, MLHoudiniCounterexampleCollector>> impl2ErrorHandler;

        // Essentials: VCGen, Prover
        VCGen vcgen;
        ProverInterface prover;

        #region Horn

        /// <summary>
        /// The filename of the Boogie program being verified.
        /// </summary>
        string filename;

        /// <summary>
        /// String containing the filename (potentially including the complete path) the the learner's executable.
        /// </summary>
        string learnerExecutable;

        /// <summary>
        /// String containing all options that are passed to the learner.
        /// </summary>
        string learnerOptions;

        /// <summary>
        /// Indicates whether to use bounds on integer variables when searching for counterexamples.
        /// </summary>
        bool useBounds;

        /// <summary>
        /// A list of bounds used to bound integer variables if bounding counterexamples is active.
        /// </summary>
        List<int> bounds4cex;

        #endregion

        // Stats
        TimeSpan proverTime;
        int numProverQueries;
        TimeSpan c5LearnerTime;
        int numLearnerQueries;
        TimeSpan totaltime;
        TimeSpan jsontime;

        int numPosExamples;
        int numNegExamples;
        int numHornClauses;
        int totalTreeSize;
        int lastTreeSize;
        int total_truetrue_implications;
        int last_truetrue_implications;
        int total_falsetrue_implications;
        int last_falsetrue_implications;
        int total_falsefalse_implications;
        int last_falsefalse_implications;
        //bool posNegCexAdded;

        // Z3 context for implementing the SMT-based ICE learner.
        HashSet<Tuple<List<Tuple<string, List<Model.Element>>>, List<Tuple<string, List<Model.Element>>>>> counterExamples;
        HashSet<Tuple<List<Tuple<string, List<Model.Element>>>, List<Tuple<string, List<Model.Element>>>>> implicationCounterExamples;


        #region Horn

        /// <summary>
        /// Name of the categorical attribute used to distinguish existential functions.
        /// </summary>
        public const string attributeNameOfExistentialFunctions = "$func";

        /// <summary>
        /// String used to delimit the function name and the actual attribute when creating names for attributes.
        /// </summary>
        public static string attributeDelimiter = "$";

        /// <summary>
        /// Dictionary mapping existential functions to their ID, thereby defining the order of the functions.
        /// </summary>
        Dictionary<string, int> functionID;

        /// <summary>
        /// Dictionary mapping data points to their label.
        /// </summary>
        Dictionary<dataPoint, int> c5samplePointToClassAttr;

        /// <summary>
        /// Dictionary mapping data points to their index (in the data file).
        /// </summary>
        Dictionary<dataPoint, int> c5samplePointToIndex;

        /// <summary>
        /// Number of data points (also used as the index of the next new data point).
        /// </summary>
        int c5DataPointsIndex;

        /// <summary>
        /// List of all existential functions. This list also defines the value of the categorical attribute used to distinguish between
        /// different existential functions. Hence, this can be seen as a mapping from the category to the name of the existential function.
        /// </summary>
        List<string> category2FunctionName;

        /// <summary>
        /// Dictionary mapping each existential function's attributes (i.e., names of formal parameters) to their associated expressions.
        /// </summary>
        Dictionary<string, Dictionary<string, Expr>> attribute2Expr;

        /// <summary>
        /// Horn clauses, given as tuple of indexes of data points on the left-hand-side and right-hand-side.
        /// Note that the right-hand-side of a Horn clause can be empty. This is modeled by a nullable integer type,
        /// which can be null.
        /// </summary>
        List<Tuple<List<int>, int?>> hornClauses;

        #endregion


        // flags to track the outcome of validity of a VC
        bool VCisValid;
        //bool realErrorEncountered;
        //bool newSamplesAdded;   // tracks whether new ICE samples added in a round or not?

        public MLHoudini(Program program, string learnerExecutable, string filename, string learnerOptions, bool useBounds)
        {
            this.program = program;
            this.impl2VC = new Dictionary<string, VCExpr>();
            this.impl2FuncCalls = new Dictionary<string, List<Tuple<string, Function, NAryExpr>>>();
            this.existentialFunctions = new Dictionary<string, Function>();
            this.name2Impl = new Dictionary<string, Implementation>();
            this.impl2functionsAsserted = new Dictionary<string, HashSet<string>>();
            this.impl2functionsAssumed = new Dictionary<string, HashSet<string>>();
            this.function2implAsserted = new Dictionary<string, HashSet<string>>();
            this.function2implAssumed = new Dictionary<string, HashSet<string>>();
            this.impl2ErrorHandler = new Dictionary<string, Tuple<ProverInterface.ErrorHandler, MLHoudiniCounterexampleCollector>>();
            this.constant2FuncCall = new Dictionary<string, NAryExpr>();

            // Find the existential functions
            foreach (var func in program.TopLevelDeclarations.OfType<Function>()
                .Where(f => QKeyValue.FindBoolAttribute(f.Attributes, "existential")))
                existentialFunctions.Add(func.Name, func);

            // extract the constants in the program to determine the range for the template domain elements
            this.function2Value = new Dictionary<string, MLICEDomain>();
            foreach (var func in existentialFunctions.Values)
            {
                function2Value[func.Name] = new DecisionTreeDomain(func.InParams);
            }

            counterExamples = new HashSet<Tuple<List<Tuple<string, List<Model.Element>>>, List<Tuple<string, List<Model.Element>>>>>();
            implicationCounterExamples = new HashSet<Tuple<List<Tuple<string, List<Model.Element>>>, List<Tuple<string, List<Model.Element>>>>>();
            bounds4cex = new List<int>();
            this.filename = filename;
            this.learnerExecutable = learnerExecutable;
            this.learnerOptions = learnerOptions;
            this.useBounds = useBounds;

            // config = alg1, alg2, alg3, alg4, smallcex_alg1, smallcex_alg2, ...

            if (this.useBounds)
            {
                bounds4cex.Add(2);
                bounds4cex.Add(5);
                bounds4cex.Add(10);
            }

            existentialFunctions.Keys.Iter(f => function2implAssumed.Add(f, new HashSet<string>()));
            existentialFunctions.Keys.Iter(f => function2implAsserted.Add(f, new HashSet<string>()));

            // type check
            existentialFunctions.Values.Iter(func =>
                {
                    if (func.OutParams.Count != 1 || !func.OutParams[0].TypedIdent.Type.IsBool)
                        throw new MLHoudiniInternalError(string.Format("Existential function {0} must return bool", func.Name));
                    if (func.Body != null)
                        throw new MLHoudiniInternalError(string.Format("Existential function {0} should not have a body", func.Name));
                    func.InParams.Iter(v =>
                    {
                        if (!v.TypedIdent.Type.IsInt && !v.TypedIdent.Type.IsBool)
                        {
                            throw new MLHoudiniInternalError("TypeError: Illegal tpe, expecting int or bool");
                        }
                    });
                });

            Inline();

            this.vcgen = new VCGen(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, new List<Checker>());
            this.prover = ProverInterface.CreateProver(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, CommandLineOptions.Clo.ProverKillTime);

            this.proverTime = TimeSpan.Zero;
            this.numProverQueries = 0;
            this.c5LearnerTime = TimeSpan.Zero;
            this.numLearnerQueries = 0;
            this.totaltime = TimeSpan.Zero;
            this.jsontime = TimeSpan.Zero;

            this.numPosExamples = 0;
            this.numNegExamples = 0;
            this.numHornClauses = 0;
            this.total_falsefalse_implications = 0;
            this.total_falsetrue_implications = 0;
            this.total_truetrue_implications = 0;
            this.totalTreeSize = 0;
            this.last_falsefalse_implications = 0;
            this.last_falsetrue_implications = 0;
            this.last_truetrue_implications = 0;
            this.lastTreeSize = 0;
            //this.posNegCexAdded = false;

#if C5
            this.c5DataPointsIndex = 0;
            this.c5samplePointToClassAttr = new Dictionary<dataPoint, int>();
            this.c5samplePointToIndex = new Dictionary<dataPoint, int>();
#endif

            #region Horn
            hornClauses = new List<Tuple<List<int>, int?>>();
            #endregion


            var impls = program.TopLevelDeclarations.OfType<Implementation>().Where(
                    impl => impl != null && CommandLineOptions.Clo.UserWantsToCheckRoutine(cce.NonNull(impl.Name)) && !impl.SkipVerification);

            /*
            program.TopLevelDeclarations.OfType<Implementation>()
                .Where(impl => !impl.SkipVerification)
                .Iter(impl => name2Impl.Add(impl.Name, impl));
            */

            impls.Iter(impl => name2Impl.Add(impl.Name, impl));


            #region Horn

            // Initialize attribute-to-expression map
            attribute2Expr = new Dictionary<string, Dictionary<string, Expr>>();

            // Initialize mapping of categorical value to function name
            category2FunctionName = new List<string>(existentialFunctions.Keys);
            // Also initialize reverse mapping
            functionID = new Dictionary<string, int>();
            for (int i = 0; i < category2FunctionName.Count; ++i)
            {
                functionID.Add(category2FunctionName[i], i);
            }

            // Create attributes file for the Horn learner
            GenerateAttributesFile();

            // Generare Intervals file
            GenerateIntervalsFile();

            #endregion


            // Let's do VC Gen (and also build dependencies)
            name2Impl.Values.Iter(GenVC);

        }


        #region Horn

        // Creates an interval file
        private void GenerateIntervalsFile()
        {

            StringBuilder file_content = new StringBuilder();
            int left = 0;
            int right = 0;

            //
            // Generate intervals
            //
            for (int funcIndex = 0; funcIndex < category2FunctionName.Count; ++funcIndex)
            {

                // Get function name
                var functionName = category2FunctionName[funcIndex];

                // Count attributes
                int num_bool_args = 0;
                int num_int_args = 0;
                foreach (var param in existentialFunctions[functionName].InParams)
                {

                    if (param.TypedIdent.Type.IsBool)
                    {
                        num_bool_args += 1;
                    }
                    else if (param.TypedIdent.Type.IsInt)
                    {
                        num_int_args += 1;
                    }
                    else
                    {
                        throw new MLHoudiniInternalError("Existential Functions must have either Boolean or Int typed arguments!");
                    }

                }
                var num_parameters = num_bool_args + num_int_args * num_int_args; // num_bool_args + num_int_args + 2 * num_int_args * (num_int_args - 1) / 2

                Console.WriteLine("#parameters: " + num_parameters);

                // Update right interval bound
                right = left + num_parameters - 1;

                // Add line
                file_content.AppendLine(left + "," + right);

                // Update left Interval bound
                left = right + 1;

            }

            // Write Intervals file
            using (System.IO.StreamWriter sw = System.IO.File.CreateText(filename + ".intervals"))
            {
                sw.WriteLine(file_content);
            }

        }


        // Creates an attributes file for the horn learner
        private void GenerateAttributesFile()
        {

            // Use a string builder instead of a string to speed up creating the file content
            StringBuilder file_content = new StringBuilder();


            //
            // Attribute to indicating the function to synthesize
            //
            file_content.AppendLine("cat," + attributeNameOfExistentialFunctions + "," + existentialFunctions.Count);


            //
            // Create attributes and derived attributes for each function in the order of how they are stored in category2FunctionName
            //
            for (int funcIndex = 0; funcIndex < category2FunctionName.Count; ++funcIndex)
            {

                // Get function name
                var functionName = category2FunctionName[funcIndex];

                // Get list of parameters
                List<Variable> parameters = existentialFunctions[functionName].InParams;

                // Prepare data structure to store expression for attributes
                Dictionary<string, Expr> att2Expr = new Dictionary<string, Expr>();


                //
                // Create attribute for each variable
                //
                for (int i = 0; i < parameters.Count; ++i)
                {

                    // Check if correct type of variable
                    if (!(parameters[i].TypedIdent.Type.IsBool || parameters[i].TypedIdent.Type.IsInt))
                    {
                        throw new MLHoudiniInternalError("Existential Functions must have either Boolean or Int typed arguments!");
                    }

                    // Add attribute to attributes file
                    var attributeName = functionName + attributeDelimiter + parameters[i].Name;
                    file_content.AppendLine("int," + attributeName);

                    // Create ans store expression of attribute
                    var attributeExpr = Expr.Ident(parameters[i]);
                    Debug.Assert(attributeExpr.ShallowType.IsInt || attributeExpr.ShallowType.IsBool);
                    att2Expr.Add(attributeName, attributeExpr);

                }


                //
                // Create derived attributes
                // Here we use octagonal constraints of the form x -/+ y
                //
                for (int i = 0; i < parameters.Count; ++i)
                {
                    if (parameters[i].TypedIdent.Type.IsInt)
                    {

                        for (int j = i + 1; j < parameters.Count; ++j)
                        {

                            // If both paramaters are int, create octagonal constraints
                            if (parameters[j].TypedIdent.Type.IsInt)
                            {

                                // x_i + x_j
                                var addAttributeName = attrPrefix + functionName + attributeDelimiter + parameters[i].Name + "+" + parameters[j].Name;
                                file_content.AppendLine("int," + addAttributeName);
                                att2Expr.Add(addAttributeName, Expr.Add(Expr.Ident(parameters[i]), Expr.Ident(parameters[j])));

                                // x_i + x_j
                                var subtractAttributeName = attrPrefix + functionName + attributeDelimiter + parameters[i].Name + "-" + parameters[j].Name;
                                file_content.AppendLine("int," + subtractAttributeName);
                                att2Expr.Add(subtractAttributeName, Expr.Sub(Expr.Ident(parameters[i]), Expr.Ident(parameters[j])));

                            }

                        }

                    }

                }


                //
                // Update attributes-to-exression map
                // 
                attribute2Expr.Add(functionName, att2Expr);


                //
                // Write attributes file
                //
                using (System.IO.StreamWriter sw = System.IO.File.CreateText(filename + ".attributes"))
                {
                    sw.WriteLine(file_content);
                }

            }

        }

        #endregion


        private void setupC5()
        {
            string namesFile = "";
            string intervalsFile = "";
            int lowerInterval = 2, upperInterval = 2;

            namesFile += "invariant.\n";
            // output pcs
            // pc : pc1,pc2,pc3,pc4.
            namesFile += pcAttrName + " : ";
            {
                int i = 0;
                foreach (var functionName in existentialFunctions.Keys)
                {
                    namesFile += functionName + (i < existentialFunctions.Keys.Count - 1 ? "," : "");
                    i++;
                }

                // If there exists only one existential function, we need to add a dummy function to fool the C5 learner, which does not allow a discrete attribute with just one attribute value
                if (i == 1)
                {
                    namesFile += "," + pcAttrName + "_dummy";
                }

                namesFile += "." + Environment.NewLine;

            }

            attribute2Expr = new Dictionary<string, Dictionary<string, Expr>>();
            functionID = new Dictionary<string, int>();

            foreach (var funTup in existentialFunctions)
            {
                Dictionary<string, Expr> newentry = new Dictionary<string, Expr>();
                List<Variable> args = funTup.Value.InParams;

                foreach (var variable in args)
                {
                    if (variable.TypedIdent.Type.IsBool || variable.TypedIdent.Type.IsInt)
                    {
                        newentry[funTup.Key + "$" + variable.Name] = Expr.Ident(variable);
                        Debug.Assert(newentry[funTup.Key + "$" + variable.Name].ShallowType.IsInt || newentry[funTup.Key + "$" + variable.Name].ShallowType.IsBool);
                        namesFile += funTup.Key + "$" + variable.Name + ": continuous.\n";
                        upperInterval++;
                    }
                    else
                    {
                        throw new MLHoudiniInternalError("Existential Functions should have either Boolean or Int typed arguments!");
                    }
                }


                // Commented out right now
                #region Introducing attributes with arbitrary number of variables
                /*
                int num = args.Count();
                int[] array = new int[num];
                for (int i = 0; i < num; i++)
                    array[i] = 0;

                int done = 0;
                while (true)
                {
                    for (int i = 0; i < num; i++)
                    {
                        if (array[i] < 2)
                        {
                            array[i]++;
                            break;
                        }
                        else if (i == num - 1)
                        {
                            done = 1;
                            break;
                        }
                        else
                        {
                            array[i] = 0;
                        }
                    }

                    if (done == 1)
                        break;
                    
                    int numArgs = 0;
                    for (int i = 0; i < num; i++)
                    {
                        if (array[i] != 0)
                            numArgs++;                        
                    }

                    if (numArgs == 1)
                        continue;

                    int j = 0;
                    Expr attrexpr = null;
                    string lhs = null;
                    string rhs = null;

                   
                        foreach (var variable in args)
                        {
                            if (array[j] == 1)
                            {
                                Variable var = args.ElementAt(j);
                                if (attrexpr == null)
                                {
                                    attrexpr = Expr.Ident(var);
                                }
                                else
                                {
                                    attrexpr = Expr.Add(attrexpr, Expr.Ident(var));
                                }

                                if (lhs == null)
                                {
                                    lhs = attrPrefix + funTup.Key + "$" + "+" + var.Name;
                                }
                                else
                                {
                                    lhs = lhs + "+" + var.Name;
                                }

                                if (rhs == null)
                                {
                                    rhs = "+" + funTup.Key + "$" + var.Name;
                                }
                                else
                                {
                                    rhs = rhs + "+" + funTup.Key + "$" + var.Name;
                                }

                                
                            }

                            else if (array[j] == 2)
                            {
                                Variable var = args.ElementAt(j);
                                if (attrexpr == null)
                                {
                                    attrexpr = Expr.Sub(Expr.Literal(0), Expr.Ident(var));
                                }
                                else
                                {
                                    attrexpr = Expr.Sub(attrexpr, Expr.Ident(var));
                                }

                                if (lhs == null)
                                {
                                    lhs = attrPrefix + funTup.Key + "$" + "-" + var.Name;
                                }
                                else
                                {
                                    lhs = lhs + "-" + var.Name;
                                }

                                if (rhs == null)
                                {
                                    rhs = "-" + funTup.Key + "$" + var.Name;
                                }
                                else
                                {
                                    rhs = rhs + "-" + funTup.Key + "$" + var.Name;
                                }                                
                            }
                            j++;
                        }

                        newentry[lhs] = attrexpr;
                        Debug.Assert(newentry[lhs].ShallowType.IsInt || newentry[lhs].ShallowType.IsBool);
                        namesFile += lhs + ":= " + rhs + ".\n";

                        upperInterval++;
                        

                }
                 * */
                #endregion Introducing attributes with arbitrary number of variables



                // Add implicitly defined attributes of the form x1 +/- x2
                for (int i = 0; i < args.Count; i++)
                {
                    for (int j = i + 1; j < args.Count; j++)
                    {
                        Variable var1 = args.ElementAt(i);
                        Variable var2 = args.ElementAt(j);
                        if (var1.TypedIdent.Type.IsInt && var2.TypedIdent.Type.IsInt)
                        {
                            newentry[attrPrefix + funTup.Key + "$" + var1.Name + "+" + var2.Name] = Expr.Add(Expr.Ident(var1), Expr.Ident(var2));
                            Debug.Assert(newentry[attrPrefix + funTup.Key + "$" + var1.Name + "+" + var2.Name].ShallowType.IsInt || newentry[attrPrefix + funTup.Key + "$" + var1.Name + "+" + var2.Name].ShallowType.IsBool);
                            newentry[attrPrefix + funTup.Key + "$" + var1.Name + "-" + var2.Name] = Expr.Sub(Expr.Ident(var1), Expr.Ident(var2));
                            Debug.Assert(newentry[attrPrefix + funTup.Key + "$" + var1.Name + "-" + var2.Name].ShallowType.IsInt || newentry[attrPrefix + funTup.Key + "$" + var1.Name + "-" + var2.Name].ShallowType.IsBool);
                            namesFile += attrPrefix + funTup.Key + "$" + var1.Name + "+" + var2.Name + ":= " + funTup.Key + "$" + var1.Name + " + " + funTup.Key + "$" + var2.Name + ".\n";
                            namesFile += attrPrefix + funTup.Key + "$" + var1.Name + "-" + var2.Name + ":= " + funTup.Key + "$" + var1.Name + " - " + funTup.Key + "$" + var2.Name + ".\n";
                            upperInterval += 2;
                        }
                    }
                }


                attribute2Expr[funTup.Key] = newentry;
                functionID[funTup.Key] = functionID.Count;                
                intervalsFile += lowerInterval.ToString() + " " + (upperInterval-1).ToString() + "\n";
                lowerInterval = upperInterval;
                upperInterval = lowerInterval;
            }

            namesFile += "invariant: true, false.\n";
            
            using (System.IO.StreamWriter sw = System.IO.File.CreateText(filename + ".names"))
            {
                sw.WriteLine(namesFile);
            }
            using (System.IO.StreamWriter sw = System.IO.File.CreateText(filename + ".intervals"))
            {
                if (existentialFunctions.Count == 1)
                {
                    intervalsFile += "2 2";
                }
                sw.WriteLine(intervalsFile);
            }
            
            return;
        }

        private VCGenOutcome LearnInv(Dictionary<string, int> impl2Priority)
        {
            var worklist = new SortedSet<Tuple<int, string>>();
            name2Impl.Keys.Iter(k => worklist.Add(Tuple.Create(impl2Priority[k], k)));
            
            while (worklist.Any())
            {
                var impl = worklist.First().Item2;
                worklist.Remove(worklist.First());

                #region vcgen

                var gen = prover.VCExprGen;
                var terms = new List<Expr>();
                foreach (var tup in impl2FuncCalls[impl])
                {
                    var controlVar = tup.Item2;
                    var exprVars = tup.Item3;
                    var varList = new List<Expr>();
                    exprVars.Args.OfType<Expr>().Iter(v => varList.Add(v));

                    var args = new List<Expr>();
                    controlVar.InParams.Iter(v => args.Add(Expr.Ident(v)));
                    Expr term = Expr.Eq(new NAryExpr(Token.NoToken, new FunctionCall(controlVar), args),
                                 function2Value[tup.Item1].Gamma(varList));

                    if (controlVar.InParams.Count != 0)
                    {
                        term = new ForallExpr(Token.NoToken, new List<Variable>(controlVar.InParams.ToArray()),
                            new Trigger(Token.NoToken, true, new List<Expr> { new NAryExpr(Token.NoToken, new FunctionCall(controlVar), args) }),
                            term);
                    }
                    terms.Add(term);

                    /*
                    foreach (var variable in varList)
                    {
                        terms.Add(Expr.Le(variable, Expr.Literal(10)));
                        terms.Add(Expr.Ge(variable, Expr.Literal(-10)));
                    }
                    */
                }
                var env = BinaryTreeAnd(terms, 0, terms.Count - 1);

                env.Typecheck(new TypecheckingContext((IErrorSink)null));
                var envVC = prover.Context.BoogieExprTranslator.Translate(env);
                var vc = gen.Implies(envVC, impl2VC[impl]);

                if (CommandLineOptions.Clo.Trace)
                {
                    Console.WriteLine("Verifying {0}: ", impl);
                    //Console.WriteLine("env: {0}", envVC);
                    var envFuncs = new HashSet<string>();
                    impl2FuncCalls[impl].Iter(tup => envFuncs.Add(tup.Item1));
                    envFuncs.Iter(f => PrintFunction(existentialFunctions[f]));
                }

                #endregion vcgen

                VCExpr finalVC;
                bool hasIntegerVariable = true;

                for (int i = 0; i <= bounds4cex.Count(); i++)
                {
#region boundcexvalues
                    // If there are no integer variables, then ensure the loop is only run once.
                    if (!hasIntegerVariable)
                        continue;

                    /* Last iteration is when there are enforced no bounds on the cex values. */
                    if (i < bounds4cex.Count())
                    {
                        int bound = bounds4cex.ElementAt(i);
                        terms.Clear();
                        foreach (var tup in impl2FuncCalls[impl])
                        {
                            var exprVars = tup.Item3;
                            var varList = new List<Expr>();
                            exprVars.Args.OfType<Expr>().Where(v => v.Type.IsInt).Iter(v => varList.Add(v));
                            foreach (var variable in varList)
                            {
                                terms.Add(Expr.Le(variable, Expr.Literal(bound)));
                                terms.Add(Expr.Ge(variable, Expr.Literal(-1 * bound)));
                                //terms.Add(Expr.Ge(variable, Expr.Literal(0)));
                            }
                        }
                        if (terms.Count == 0)
                        {
                            // There is no integer argument to the function to learn
                            hasIntegerVariable = false;
                        }

                        var boundcex = BinaryTreeAnd(terms, 0, terms.Count - 1);
                        boundcex.Typecheck(new TypecheckingContext((IErrorSink)null));
                        var boundcexVC = prover.Context.BoogieExprTranslator.Translate(boundcex);

                        finalVC = gen.Implies(boundcexVC, vc);
                    }
                    else
                    {
                        if (!this.useBounds)
                        {
                            finalVC = vc;
                        }
                        else
                        {
                            int bound = 1000000;
                            terms.Clear();
                            foreach (var tup in impl2FuncCalls[impl])
                            {
                                var exprVars = tup.Item3;
                                var varList = new List<Expr>();
                                exprVars.Args.OfType<Expr>().Where(v => v.Type.IsInt).Iter(v => varList.Add(v));
                                foreach (var variable in varList)
                                {
                                    terms.Add(Expr.Le(variable, Expr.Literal(bound)));
                                    terms.Add(Expr.Ge(variable, Expr.Literal(-1 * bound)));
                                    //terms.Add(Expr.Ge(variable, Expr.Literal(0)));
                                }
                            }
                            var boundcex = BinaryTreeAnd(terms, 0, terms.Count - 1);
                            boundcex.Typecheck(new TypecheckingContext((IErrorSink)null));
                            var boundcexVC = prover.Context.BoogieExprTranslator.Translate(boundcex);

                            finalVC = gen.Implies(boundcexVC, vc);
                        }
                    }
#endregion boundcexvalues

                    var handler = impl2ErrorHandler[impl].Item1;
                    var collector = impl2ErrorHandler[impl].Item2;
                    collector.Reset(impl);
                    implicationCounterExamples.Clear();
                    VCisValid = true;   // set to false if control reaches HandleCounterExample
                    //realErrorEncountered = false;
                    //newSamplesAdded = false;
                    //this.posNegCexAdded = false;

                    var start = DateTime.Now;

                    prover.Push();
                    prover.Assert(gen.Not(finalVC), true);
                    prover.FlushAxiomsToTheoremProver();
                    prover.Check();
                    ProverInterface.Outcome proverOutcome = prover.CheckOutcomeCore(handler);

                    var inc = (DateTime.Now - start);
                    proverTime += inc;
                    numProverQueries++;

                    if (CommandLineOptions.Clo.Trace)
                        Console.WriteLine("Prover Time taken = " + inc.TotalSeconds.ToString());

                    if (proverOutcome == ProverInterface.Outcome.TimeOut || proverOutcome == ProverInterface.Outcome.OutOfMemory)
                    {
                        Console.WriteLine("Z3 Prover for implementation {0} times out or runs out of memory !", impl);
                        return new VCGenOutcome(proverOutcome, new List<Counterexample>());
                    }

                    if (!VCisValid)
                    {
                        /* There was a counterexample found and acted upon while proving the method. */
                        if (collector.real_errors.Count > 0)
                        {
                            return new VCGenOutcome(ProverInterface.Outcome.Invalid, collector.real_errors);
                        }

                        if (collector.conjecture_errors.Count == 0)
                        {
                            // No positive or negative counter-example added. Need to add implication counter-examples
                            Debug.Assert(collector.implication_errors.Count > 0);
                            foreach (var cex in implicationCounterExamples)
                            {
                                AddCounterExample(cex);
                            }
                        }

                        //Debug.Assert(newSamplesAdded);
                        HashSet<string> funcsChanged;

                        if (!learn(out funcsChanged))
                        {
                            // learner timed out, ran into some errors, or if there is no consistent conjecture
                            prover.Pop();
                            if(collector.conjecture_errors.Count > 0)
                                return new VCGenOutcome(ProverInterface.Outcome.Invalid, collector.conjecture_errors);
                            else
                                return new VCGenOutcome(ProverInterface.Outcome.Invalid, collector.implication_errors);
                        }
                        // propagate dependent guys back into the worklist, including self
                        var deps = new HashSet<string>();
                        deps.Add(impl);
                        funcsChanged.Iter(f => deps.UnionWith(function2implAssumed[f]));
                        funcsChanged.Iter(f => deps.UnionWith(function2implAsserted[f]));

                        deps.Iter(s => worklist.Add(Tuple.Create(impl2Priority[s], s)));

                        // break out of the loop that iterates over various bounds.
                        prover.Pop();
                        break;
                    }
                    else
                    {
                        prover.Pop();
                    }
                }
            }
            // The program was verified
            return new VCGenOutcome(ProverInterface.Outcome.Valid, new List<Counterexample>());            
        }


        public VCGenOutcome ComputeSummaries()
        {
            // Compute SCCs and determine a priority order for impls
            var Succ = new Dictionary<string, HashSet<string>>();
            var Pred = new Dictionary<string, HashSet<string>>();
            name2Impl.Keys.Iter(s => Succ[s] = new HashSet<string>());
            name2Impl.Keys.Iter(s => Pred[s] = new HashSet<string>());

            foreach(var impl in name2Impl.Keys) {
                Succ[impl] = new HashSet<string>();
                impl2functionsAsserted[impl].Iter(f => 
                    function2implAssumed[f].Iter(succ =>
                        {
                            Succ[impl].Add(succ);
                            Pred[succ].Add(impl);
                        }));
            }

            var sccs = new StronglyConnectedComponents<string>(name2Impl.Keys,
                new Adjacency<string>(n => Pred[n]),
                new Adjacency<string>(n => Succ[n]));
            sccs.Compute();
            
            // impl -> priority
            var impl2Priority = new Dictionary<string, int>();
            int p = 0;
            foreach (var scc in sccs)
            {
                foreach (var impl in scc)
                {
                    impl2Priority.Add(impl, p);
                    p++;
                }
            }

            VCGenOutcome overallOutcome = null;

            var start = DateTime.Now;

            overallOutcome = LearnInv(impl2Priority);

            var elapsed = DateTime.Now;
            this.totaltime = elapsed - start;

            if (true)
            {
                Console.WriteLine("Prover time = {0}", proverTime.TotalSeconds.ToString("F2"));
                Console.WriteLine("Number of prover queries = " + numProverQueries);
                Console.WriteLine("Learner time = {0}", c5LearnerTime.TotalSeconds.ToString("F2"));
                //Console.WriteLine("time to parse JSON and construct Boogie Model = {0}", jsontime.TotalSeconds.ToString("F2"));
                Console.WriteLine("Number of learner queries = " + numLearnerQueries);

                //Console.WriteLine("Total time: {0}", proverTime.Add(c5LearnerTime).TotalSeconds.ToString("F2"));
                Console.WriteLine("Total time: {0}", totaltime.Subtract(jsontime).TotalSeconds.ToString("F2"));

                Console.WriteLine("Number of positive examples:" + this.numPosExamples);
                Console.WriteLine("Number of negative examples:" + this.numNegExamples);
                Console.WriteLine("Number of Horn clauses:" + this.numHornClauses);

                /*Console.WriteLine("Average tree size: " + ((double)this.totalTreeSize / (double)this.c5LearnerQueries));
                Console.WriteLine("Last tree size: " + this.lastTreeSize);
                Console.WriteLine("Average truetrue implications: " + ((double)this.total_truetrue_implications / (double)this.c5LearnerQueries));
                Console.WriteLine("last truetrue implications: " + this.last_truetrue_implications);
                Console.WriteLine("Average falsetrue implications: " + ((double)this.total_falsetrue_implications/ (double)this.c5LearnerQueries));
                Console.WriteLine("last falsetrue implications: " + this.last_falsetrue_implications);
                Console.WriteLine("Average falsefalse implications: " + ((double)this.total_falsefalse_implications / (double)this.c5LearnerQueries));
                Console.WriteLine("last falsefalse implications: " + this.last_falsefalse_implications);                */
            }

            if (CommandLineOptions.Clo.PrintAssignment)
            {
                // Print the existential functions
                existentialFunctions.Values.Iter(PrintFunction);
            }


            //
            // Statistics output
            //
            using (System.IO.StreamWriter sw = System.IO.File.CreateText(filename + ".statistics"))
            {
                sw.WriteLine(System.IO.Path.GetFileName(filename) + "," + numLearnerQueries + "," + numPosExamples + "," + numNegExamples + "," + numHornClauses + "," + c5LearnerTime.TotalSeconds.ToString("F2") + "," + totaltime.TotalSeconds.ToString("F2"));
            }


            return overallOutcome;
        }

        private static Expr BinaryTreeAnd(List<Expr> terms, int start, int end)
        {
            if (start > end)
                return Expr.True;
            if (start == end)
                return terms[start];
            if (start + 1 == end)
                return Expr.And(terms[start], terms[start + 1]);
            var mid = (start + end) / 2;
            return Expr.And(BinaryTreeAnd(terms, start, mid), BinaryTreeAnd(terms, mid + 1, end));
        }

        /*
        public IEnumerable<Function> GetAssignment()
        {
            var ret = new List<Function>();
            foreach (var func in existentialFunctions.Values)
            {
                var invars = new List<Expr>(func.InParams.OfType<Variable>().Select(v => Expr.Ident(v)));
                func.Body = function2Value[func.Name].Gamma(invars);
                ret.Add(func);
            }
            return ret;
        }
        */

        private void PrintFunction(Function function)
        {
            var tt = new TokenTextWriter(Console.Out);
            var invars = new List<Expr>(function.InParams.OfType<Variable>().Select(v => Expr.Ident(v)));
            function.Body = function2Value[function.Name].Gamma(invars);
            function.Emit(tt, 0);
            tt.Close();
        }

        public string outputDataPoint(dataPoint p)
        {
            string funcName = p.functionName;
            List<int> attrVals = p.value;
            string ret = funcName;
            foreach (var exFunc in existentialFunctions)
            {
                if (exFunc.Key.Equals(funcName))
                {
                    foreach (var x in attrVals)
                    {
                        ret += "," + x.ToString();
                    }
                }
                else
                {
                    foreach (var arg in exFunc.Value.InParams)
                    {
                        ret += ",?";
                    }
                }
            }
            return ret;
        }

        /*
        public void RecordCounterExamples2File(Tuple<List<Tuple<string, List<Model.Element>>>, List<Tuple<string, List<Model.Element>>>> cex)
        {
            List<Tuple<string, List<Model.Element>>> lhs = cex.Item1;
            List<Tuple<string, List<Model.Element>>> rhs = cex.Item2;

            string ret = "";
            
            if (lhs.Count == 0)
            {
                Debug.Assert(rhs.Count == 1);
                ret += ParseListOfModel(rhs.ElementAt(0).Item2);
                ret += ";accept";
            }
            else if (rhs.Count == 0)
            {
                Debug.Assert(lhs.Count == 1);
                ret += ParseListOfModel(lhs.ElementAt(0).Item2);
                ret += ";reject";
            }
            else
            {
                Debug.Assert(lhs.Count == 1);
                Debug.Assert(rhs.Count == 1);
                ret += ParseListOfModel(lhs.ElementAt(0).Item2);
                ret += ";antecedent\n";
                ret += ParseListOfModel(rhs.ElementAt(0).Item2);
                ret += ";consequent";
            }
            if (!System.IO.File.Exists("samples.txt"))
            {
                // Create a file to write to. 
                using (System.IO.StreamWriter sw = System.IO.File.CreateText("samples.txt"))
                {
                    sw.WriteLine("// x y -- empty line");                    
                }
            }

            // This text is always added, making the file longer over time 
            // if it is not deleted. 
            using (System.IO.StreamWriter sw = System.IO.File.AppendText("samples.txt"))
            {                
                sw.WriteLine(ret);
            }
            return;
        }
         * */

#if C5
        public void RecordCexForC5(Tuple<List<Tuple<string, List<Model.Element>>>, List<Tuple<string, List<Model.Element>>>> cex, bool recordHornClause = true)
        {

            // A counterexample is a tuple (lhs, rhs), interpreted as implication, where lhs and rhs are
            // both lists of data points. In MLHoudini's internal representation, a data point is a pair consisting of
            // a function name (given as string) and a list of model values (the values of the formal parameters of
            // the existential function in the order of their appearance).
            // 
            // MLHoudini's internal representation of a data point is converted to a data point object and stored. The
            // conversion itself happens in the constructor of the data point.
            //
            // A counterexample is extracted from a model of (the negation of) a verification condition (VC). The form of
            // a VC is that there are several assume statements and one assert statement. If an assume statement involves
            // an existential function, it is added to lhs. If the assert statement involves an existential function, it
            // it is added to rhs. Thus, a counterexample can have 0-n data points on the left hand side and 0-1 data
            // points on the right hand side. The following situations are legal (and should be the only occurring):
            //
            // - 0 data point in lhs and 1 data point in rhs: this corresponds to a positive counterexample
            // - 1 data point in lhs and 0 data point in rhs: this corresponds to a negative counterexample
            // - 1-n data point in lhs and 1 data point in rhs: this corresponds to a Horn counterexample


            List<Tuple<string, List<Model.Element>>> lhs = cex.Item1;
            List<Tuple<string, List<Model.Element>>> rhs = cex.Item2;


            //
            // Positive counterexample
            //
            if (lhs.Count == 0 && rhs.Count == 1)
            {

                //Debug.Assert(rhs.Count == 1);
                
                // Create data point from VC model
                dataPoint dp = new dataPoint(rhs.ElementAt(0).Item1, rhs.ElementAt(0).Item2);

                // Data point already exists, but then needs to be unlabeled
                if (c5samplePointToIndex.ContainsKey(dp))
                {

                    // Check that the data point is not labeled with false
                    Debug.Assert(c5samplePointToClassAttr[dp] != 2); // should be unknown

                    // Change label to positive
                    c5samplePointToClassAttr[dp] = 1;

                    // Output action
                    if (CommandLineOptions.Clo.Trace)
                    {
                        Console.WriteLine("Overwrote: " + dp.print() + ": positive");
                    }

                }

                // Data point is new
                else
                {

                    // Add data point (i.e., give it a unique ID / index and attach a label)
                    c5samplePointToIndex[dp] = c5DataPointsIndex;
                    c5DataPointsIndex++;
                    c5samplePointToClassAttr[dp] = 1;

                    // Output action
                    if (CommandLineOptions.Clo.Trace)
                    {
                        Console.WriteLine("Added: " + dp.print() + ": positive");
                    }

                }

                ++numPosExamples;

            }


            //
            // Negative counterexample
            //
            else if (lhs.Count == 1 && rhs.Count == 0)
            {

                /*
                 * Goes away
                if(lhs.Count > 1)
                {
                    List<Tuple<string, List<Model.Element>>> newlhs = new List<Tuple<string, List<Model.Element>>>();
                    newlhs.Add(lhs.ElementAt(lhs.Count - 1));
                    lhs = newlhs;
                }
                Debug.Assert(lhs.Count == 1);
                */


                // Create data point from VC model
                dataPoint dp = new dataPoint(lhs.ElementAt(0).Item1, lhs.ElementAt(0).Item2);

                // Data point already exists, but then needs to be unlabeled
                if (c5samplePointToIndex.ContainsKey(dp))
                {

                    // Check that the data point is not labeled with true
                    Debug.Assert(c5samplePointToClassAttr[dp] != 1); // should be unknown

                    // Change label to negative
                    c5samplePointToClassAttr[dp] = 2;

                    // Output action
                    if (CommandLineOptions.Clo.Trace)
                    {
                        Console.WriteLine("Overwrote: " + dp.print() + ": negative");
                    }

                }

                // Data point is new
                else
                {

                    // Add data point (i.e., give it a unique ID / index and attach a label)
                    c5samplePointToIndex[dp] = c5DataPointsIndex;
                    c5DataPointsIndex++;
                    c5samplePointToClassAttr[dp] = 2;

                    // Output action
                    if (CommandLineOptions.Clo.Trace)
                    {
                        Console.WriteLine("Added: " + dp.print() + ": negative");
                    }

                }

                ++numNegExamples;

            }


            //
            // Horn counterexample (potentially with empty right-hand-side)
            //
            else if (lhs.Count > 0 && rhs.Count <= 1)
            {

                /*
                 * Needs to go away
                if (lhs.Count > 1)
                {
                    List<Tuple<string, List<Model.Element>>> newlhs = new List<Tuple<string, List<Model.Element>>>();
                    newlhs.Add(lhs.ElementAt(lhs.Count - 1));
                    lhs = newlhs;
                }
                Debug.Assert(lhs.Count == 1);
                Debug.Assert(rhs.Count == 1);
                */

                // List storing indexes of data points occuring on the left-hand-side of the Horn clause
                List<int> lhsIndexes = new List<int>();

                //
                // Process data points on left-hand-side
                //
                foreach (var tup in lhs)
                {

                    // Create data point
                    dataPoint lhsDataPoint = new dataPoint(tup.Item1, tup.Item2);

                    // Data point already exists
                    if (c5samplePointToIndex.ContainsKey(lhsDataPoint))
                    {
                        lhsIndexes.Add(c5samplePointToIndex[lhsDataPoint]);
                    }

                    // Data point is new
                    else
                    {

                        c5samplePointToIndex[lhsDataPoint] = c5DataPointsIndex;
                        lhsIndexes.Add(c5DataPointsIndex);
                        ++c5DataPointsIndex;
                        c5samplePointToClassAttr[lhsDataPoint] = 0;

                    }

                }

                Debug.Assert(lhs.Count == lhsIndexes.Count);


                //
                // Process data point on right-hand-side
                //
                int? rhsIndex = null;

                // If there is a data-point onb the right-hand-side, handle it and update rhsIndex
                if (rhs.Count == 1)
                {

                    // Create data point and variable to hold index of this data point
                    dataPoint rhsDataPoint = new dataPoint(rhs.ElementAt(0).Item1, rhs.ElementAt(0).Item2);
                    
                    // Data point already exists
                    if (c5samplePointToIndex.ContainsKey(rhsDataPoint))
                    {
                        rhsIndex = c5samplePointToIndex[rhsDataPoint];
                    }

                    // Data point is new
                    else
                    {

                        c5samplePointToIndex[rhsDataPoint] = c5DataPointsIndex;
                        rhsIndex = c5DataPointsIndex;
                        c5DataPointsIndex++;
                        c5samplePointToClassAttr[rhsDataPoint] = 0;

                    }

                }


                //
                // Record Horn clause ?!?
                //
                if (recordHornClause)
                {
 
                    // Output action
                    if (CommandLineOptions.Clo.Trace)
                    {

                        string lhsStr = "";
                        for (int i = 0; i < lhsIndexes.Count; ++i)
                        {
                            lhsStr += (i == 0 ? "" : " && ") + lhsIndexes[i];
                        }

                        Console.WriteLine("Added Horn clause: " + lhsStr + " => " + rhsIndex);
                    }

                    // Store Horn clause
                    hornClauses.Add(new Tuple<List<int>, int?>(lhsIndexes, rhsIndex));
                    ++numHornClauses;

                }

            }


            //
            // Error, don't know how to handle such counterexamples
            //
            else
            {
                throw new MLHoudiniInternalError("Teacher received malformed counterexample");
            }

        }


        #region Horn


        /// <summary>
        /// Generates a string representation of a given data point in the Horn learner syntax.
        /// Attributes that correspond to paramaters not in the scope of the function to which the
        /// data point belongs are set to a default value.
        /// </summary>
        /// <param name="dp">A data point</param>
        /// <returns>a string representation of a given data point in the Horn learner syntax</returns>
        private string Datapoint2String(dataPoint dp)
        {

            StringBuilder builder = new StringBuilder();
            int category = -1;

            // Iterate over all existential functions
            for (int i = 0; i < category2FunctionName.Count; ++i)
            {

                // Output values of variables belonging to the current function
                if (category2FunctionName[i].Equals(dp.functionName))
                {

                    // Remeber category of function
                    category = i;

                    // Output program values
                    foreach (var value in dp.value)
                    {
                        builder.Append(",").Append(value);
                    }

                    // Output octagonal constraints
                    for (int k = 0; k < dp.value.Count; ++k)
                    {
                        if (existentialFunctions[category2FunctionName[i]].InParams[k].TypedIdent.Type.IsInt)
                        {
                            for (int l = k + 1; l < dp.value.Count; ++l)
                            {
                                if (existentialFunctions[category2FunctionName[i]].InParams[l].TypedIdent.Type.IsInt)
                                {
                                    builder.Append(",").Append(dp.value[k] + dp.value[l]);
                                    builder.Append(",").Append(dp.value[k] - dp.value[l]);
                                }
                            }
                        }
                    }

                }

                // This part of the data point corresponds to another existential function, so just output the default value for all attributes
                else
                {
                    for (int j = 0; j < existentialFunctions[category2FunctionName[i]].InParams.Count; ++j)
                    {
                        builder.Append(",0");
                    }
                    for (int k = 0; k < existentialFunctions[category2FunctionName[i]].InParams.Count; ++k)
                    {
                        if (existentialFunctions[category2FunctionName[i]].InParams[k].TypedIdent.Type.IsInt)
                        {
                            for (int l = k + 1; l < existentialFunctions[category2FunctionName[i]].InParams.Count; ++l)
                            {
                                if (existentialFunctions[category2FunctionName[i]].InParams[l].TypedIdent.Type.IsInt)
                                {
                                    builder.Append(",0,0");
                                }
                            }
                        }
                    }
                }

            }

            Debug.Assert(category >= 0);

            return category + builder.ToString();

        }


        /// <summary>
        /// Writes the data points to file.
        /// </summary>
        private void GenerateDataFile()
        {

            StringBuilder content = new StringBuilder();

            // Create file content (i.e., write each data point)
            int pos = 0;
            foreach (var kvPair in c5samplePointToClassAttr)
            {

                // TODO (Daniel): Ensure that order of data points is correct!
                if (c5samplePointToIndex[kvPair.Key] != pos++)
                {
                    throw new MLHoudiniInternalError("Detected incorrect order of data points in data file");
                }
                
                // Output data point
                content.Append(Datapoint2String(kvPair.Key));

                // Output label
                switch (kvPair.Value)
                {

                    case 0:
                        content.AppendLine(",?");
                        break;

                    case 1:
                        content.AppendLine(",true");
                        break;

                    case 2:
                        content.AppendLine(",false");
                        break;

                    default:
                        throw new MLHoudiniInternalError("Unknown label of data point");

                }

            }

            // Write to file
            using (System.IO.StreamWriter sw = System.IO.File.CreateText(filename + ".data"))
            {
                sw.Write(content);
            }

        }


        /// <summary>
        /// Writes the Horn clauses to file.
        /// </summary>
        void GenerateHornFile()
        {

            StringBuilder content = new StringBuilder();

            // Write each Horn constraint
            foreach (var clause in hornClauses)
            {

                // Write left-hand-side
                foreach (var index in clause.Item1)
                {
                    content.Append(index).Append(',');
                }

                // Write right-hand-side
                content.AppendLine(clause.Item2 == null ? "_" : clause.Item2.ToString());

            }


            // Write to file
            using (System.IO.StreamWriter sw = System.IO.File.CreateText(filename + ".horn"))
            {
                sw.Write(content);
            }

        }

        /// <summary>
        /// Writes status information to file, allowing the teacher to communicate (optional) information
        /// to the learner. As of now, the teacher only communicates the current number of learner
        /// invocations.
        /// </summary>
        void GenerateStatusFile()
        {

            using (System.IO.StreamWriter sw = System.IO.File.CreateText(filename + ".status"))
            {
                sw.Write(numLearnerQueries);
            }

        }

        #endregion

#endif

        public void AddCounterExample(Tuple<List<Tuple<string, List<Model.Element>>>, List<Tuple<string, List<Model.Element>>>> cex, bool recordImplications = true)
        {
            List<Tuple<string, List<Model.Element>>> lhs = cex.Item1;
            List<Tuple<string, List<Model.Element>>> rhs = cex.Item2;

            //counterExamples.Add(cex);
#if false
            if (lhs.Count > 0 && rhs.Count > 0)
            {
                this.numImplications++;
                if(recordImplications && CommandLineOptions.Clo.Trace) 
                    Console.WriteLine("Horn clause added");
                else if (CommandLineOptions.Clo.Trace)
                    Console.WriteLine("Horn clause points added as unknowns (no edge added!)");                
            }
            else if (lhs.Count > 0)
            {
                this.numNegCounterExamples++;
                if (CommandLineOptions.Clo.Trace)
                    Console.WriteLine("Negative example added");
            }
            else
            {
                this.numPosExamples++;
                if (CommandLineOptions.Clo.Trace)
                    Console.WriteLine("Positive example added");
            }
#endif

#if C5
            RecordCexForC5(cex, recordImplications);
#endif
        }
        
#if Pranav
        public bool HandleCounterExample(string impl, Counterexample error, out bool counterExampleAdded)
        {
            // return true if a true error encountered.
            // return false if the error is due to a wrong choice of current conjecture.
            counterExampleAdded = false;

            VCisValid = false;
            var cex = P_ExtractState(impl, error);

            // the counter-example does not involve any existential function ==> Is a real counter-example !
            if (cex.Item1.Count == 0 && cex.Item2.Count == 0)
            {
                realErrorEncountered = true;
                return true;
            }
            if (!newSamplesAdded || (cex.Item1.Count == 1 && cex.Item2.Count == 0) || (cex.Item2.Count == 1 && cex.Item1.Count == 0))
            {
                AddCounterExample(cex);
                counterExampleAdded = true;
            }
            newSamplesAdded = true;          
            return false;
        }
#endif

        public bool HandleCounterExample(string impl, Counterexample error, out bool cexAdded)
        {
            // return true if a true error encountered.
            // return false if the error is due to a wrong choice of current conjecture.
            VCisValid = false;
            var cex = P_ExtractState(impl, error);

            // the counter-example does not involve any existential function ==> Is a real counter-example !
            if (cex.Item1.Count == 0 && cex.Item2.Count == 0)
            {
                //realErrorEncountered = true;
                cexAdded = false;
                return true;
            }

#if true
            if (cex.Item1.Count == 0 || cex.Item2.Count == 0)
            {
                cexAdded = true;
                AddCounterExample(cex);
                return false;
            }
            else
            {
                cexAdded = false;
                implicationCounterExamples.Add(cex);
                return false;
            }

            /*
            if (!this.posNegCexAdded || (cex.Item1.Count == 0 || cex.Item2.Count == 0))
            {
                // Record the cex. Is a positive or negative cex or is the first occurence of the implications
                if(cex.Item1.Count == 0 || cex.Item2.Count == 0)
                    this.posNegCexAdded = true;

                cexAdded = true;
                AddCounterExample(cex);
                newSamplesAdded = true;
                return false;
            }
            else
            {
#if false
                AddCounterExample(cex, false);
#endif
                cexAdded = false;
                return false;
            }
            */
#else
            cexAdded = true;
            AddCounterExample(cex);
            newSamplesAdded = true;
            return false;
#endif
        }


        #region Horn

        public bool learn(out HashSet<string> funcsChanged)
        {

            // Reset functions that have changed during last call to the learner (will be filled in the end)
            funcsChanged = null;

            // Update number of calls to learner
            ++numLearnerQueries;


            //
            // Generate files for Horn DT learner
            //
            GenerateDataFile();
            GenerateHornFile();
            GenerateStatusFile();


            //
            // Run learner
            //

            // Create startup info
            ProcessStartInfo learnerStartInfo = new ProcessStartInfo();
            learnerStartInfo.FileName = learnerExecutable;
            learnerStartInfo.Arguments = learnerOptions == null ? filename : learnerOptions + " " + filename;
            learnerStartInfo.WindowStyle = ProcessWindowStyle.Hidden;
            learnerStartInfo.CreateNoWindow = true;
            learnerStartInfo.UseShellExecute = false;
            //process.RedirectStandardOutput = true;
            if (CommandLineOptions.Clo.Trace)
            {
                Console.WriteLine("Calling " + learnerStartInfo.FileName + " " + learnerStartInfo.Arguments);
            }

            // Run the external process & wait for it to finish
            Process learnerProcess = Process.Start(learnerStartInfo);
            learnerProcess.WaitForExit();


            //
            // Check exit code of learner
            //
            var learnerExitCode = learnerProcess.ExitCode;
            if (learnerExitCode != 0)
            {
                Console.WriteLine("The learner seems to have run into an error!");
                throw new MLHoudiniInternalError("The learner seems to have run into an error!");
            }
            if (CommandLineOptions.Clo.Trace)
            {
                Console.WriteLine("Total learner time was " + (learnerProcess.ExitTime - learnerProcess.StartTime).ToString());
            }
            c5LearnerTime += (learnerProcess.ExitTime - learnerProcess.StartTime);


            var start = DateTime.Now;

            //
            // Read JSON tree from file
            //
            string JSONString = System.IO.File.ReadAllText(filename + ".json");
            TreeNode root = JsonConvert.DeserializeObject<TreeNode>(JSONString);
            if (root == null)
            {
                throw new MLHoudiniInternalError("Unable to read result of learner");
            }


            //
            // Generate new implementation of existential functions from decision trees
            //
            funcsChanged = new HashSet<string>();
            foreach (var functionName in function2Value.Keys)
            {
                // If the implementation of the existential function has changed, add it to the list of changed functions
                if (function2Value[functionName].constructModel(functionName, root, attribute2Expr, functionID))
                {
                    funcsChanged.Add(functionName);
                }
            }
            this.jsontime += (DateTime.Now - start);

            if (funcsChanged.Count() == 0)
            {
                return false;
            }
            else
            {
                return true;
            }


        }

        #endregion


        private List<Tuple<string, List<Model.Element>>> ExtractState(string impl, Counterexample error)
        {
            var lastBlock = error.Trace.Last() as Block;
            AssertCmd failingAssert = null;

            CallCounterexample callCounterexample = error as CallCounterexample;
            if (callCounterexample != null)
            {
                Procedure failingProcedure = callCounterexample.FailingCall.Proc;
                Requires failingRequires = callCounterexample.FailingRequires;
                failingAssert = lastBlock.Cmds.OfType<AssertRequiresCmd>().FirstOrDefault(ac => ac.Requires == failingRequires);
            }
            ReturnCounterexample returnCounterexample = error as ReturnCounterexample;
            if (returnCounterexample != null)
            {
                Ensures failingEnsures = returnCounterexample.FailingEnsures;
                failingAssert = lastBlock.Cmds.OfType<AssertEnsuresCmd>().FirstOrDefault(ac => ac.Ensures == failingEnsures);
            }
            AssertCounterexample assertCounterexample = error as AssertCounterexample;
            if (assertCounterexample != null)
            {
                failingAssert = lastBlock.Cmds.OfType<AssertCmd>().FirstOrDefault(ac => ac == assertCounterexample.FailingAssert);
            }

            Debug.Assert(failingAssert != null);
            return ExtractState(impl, failingAssert.Expr, error.Model);
        }

        private Tuple<List<Tuple<string, List<Model.Element>>>, List<Tuple<string, List<Model.Element>>>> P_ExtractState(string impl, Counterexample error)
        {
            var lastBlock = error.Trace.Last() as Block;
            AssertCmd failingAssert = null;

            CallCounterexample callCounterexample = error as CallCounterexample;
            if (callCounterexample != null)
            {
                Procedure failingProcedure = callCounterexample.FailingCall.Proc;
                Requires failingRequires = callCounterexample.FailingRequires;
                failingAssert = lastBlock.Cmds.OfType<AssertRequiresCmd>().FirstOrDefault(ac => ac.Requires == failingRequires);
            }
            ReturnCounterexample returnCounterexample = error as ReturnCounterexample;
            if (returnCounterexample != null)
            {
                Ensures failingEnsures = returnCounterexample.FailingEnsures;
                failingAssert = lastBlock.Cmds.OfType<AssertEnsuresCmd>().FirstOrDefault(ac => ac.Ensures == failingEnsures);
            }
            AssertCounterexample assertCounterexample = error as AssertCounterexample;
            if (assertCounterexample != null)
            {
                failingAssert = lastBlock.Cmds.OfType<AssertCmd>().FirstOrDefault(ac => ac == assertCounterexample.FailingAssert);
            }
            Debug.Assert(failingAssert != null);

            // extract the lhs of the returned tuple from the AssumeCmds
            List<Tuple<string, List<Model.Element>>> lhs = new List<Tuple<string, List<Model.Element>>>();
            foreach (var cmd in error.AssumedCmds) 
            {
                AssumeCmd assumeCmd = cmd as AssumeCmd;
                Debug.Assert(assumeCmd != null);
                lhs.AddRange(P_ExtractState(impl, assumeCmd.Expr, error.Model));
            }

            List<Tuple<string, List<Model.Element>>> rhs = new List<Tuple<string, List<Model.Element>>>();
            rhs = P_ExtractState(impl, failingAssert.Expr, error.Model);
            return Tuple.Create(lhs, rhs);
        }

        private List<Tuple<string, List<Model.Element>>> P_ExtractState(string impl, Expr expr, Model model)
        {
            /*
            var funcsUsed = P_FunctionCollector.Collect(expr);

            var ret = new List<Tuple<string, List<Model.Element>>>();

            foreach (var fn in funcsUsed)
            {
                var fnName = fn.Name;
                if (!constant2FuncCall.ContainsKey(fnName))
                    continue;

                var func = constant2FuncCall[fnName];
                var funcName = (func.Fun as FunctionCall).FunctionName;
                var vals = new List<Model.Element>();
                prover.Context.BoogieExprTranslator.Translate(func.Args).Iter(ve => vals.Add(getValue(ve, model)));
                ret.Add(Tuple.Create(funcName, vals));
            }
             */
            
            var funcsUsed = FunctionCollector.Collect(expr);

            var ret = new List<Tuple<string, List<Model.Element>>>();

            foreach (var tup in funcsUsed.Where(t => t.Item2 == null))
            {
                var constant = tup.Item1;
                if (!constant2FuncCall.ContainsKey(constant.Name))
                    continue;

                var func = constant2FuncCall[constant.Name];
                var funcName = (func.Fun as FunctionCall).FunctionName;
                var vals = new List<Model.Element>();
                prover.Context.BoogieExprTranslator.Translate(func.Args).Iter(ve => vals.Add(getValue(ve, model)));
                ret.Add(Tuple.Create(funcName, vals));
            }

            foreach (var tup in funcsUsed.Where(t => t.Item2 != null))
            {
                var constant = tup.Item1;
                var boundExpr = tup.Item2;

                if (!constant2FuncCall.ContainsKey(constant.Name))
                    continue;

                // There are some bound variables (because the existential function was inside an \exists).
                // We must find an assignment for bound varibles 

                // First, peice apart the existential functions
                var cd = new Duplicator();
                var tup2 = ExistentialExprModelMassage.Massage(cd.VisitExpr(boundExpr.Body));
                var be = tup2.Item1;
                Expr env = Expr.True;
                foreach (var ahFunc in tup2.Item2)
                {
                    var tup3 = impl2FuncCalls[impl].First(t => t.Item2.Name == ahFunc.Name);
                    var varList = new List<Expr>();
                    tup3.Item3.Args.OfType<Expr>().Iter(v => varList.Add(v));

                    env = Expr.And(env, function2Value[tup3.Item1].Gamma(varList));
                }
                be = Expr.And(be, Expr.Not(env));

                // map formals to constants
                var formalToConstant = new Dictionary<string, Constant>();
                foreach (var f in boundExpr.Dummies.OfType<Variable>())
                    formalToConstant.Add(f.Name, new Constant(Token.NoToken, new TypedIdent(Token.NoToken, f.Name + "@subst@" + (existentialConstCounter++), f.TypedIdent.Type), false));
                be = Substituter.Apply(new Substitution(v => formalToConstant.ContainsKey(v.Name) ? Expr.Ident(formalToConstant[v.Name]) : Expr.Ident(v)), be);
                formalToConstant.Values.Iter(v => prover.Context.DeclareConstant(v, false, null));

                var reporter = new AbstractHoudiniErrorReporter();
                var ve = prover.Context.BoogieExprTranslator.Translate(be);
                prover.Assert(ve, true);
                prover.Check();
                var proverOutcome = prover.CheckOutcomeCore(reporter);
                if (proverOutcome != ProverInterface.Outcome.Invalid)
                    continue;
                model = reporter.model;

                var func = constant2FuncCall[constant.Name];
                var funcName = (func.Fun as FunctionCall).FunctionName;
                var vals = new List<Model.Element>();
                foreach (var funcArg in func.Args.OfType<Expr>())
                {
                    var arg = Substituter.Apply(new Substitution(v => formalToConstant.ContainsKey(v.Name) ? Expr.Ident(formalToConstant[v.Name]) : Expr.Ident(v)), funcArg);
                    vals.Add(getValue(prover.Context.BoogieExprTranslator.Translate(arg), model));
                }
                ret.Add(Tuple.Create(funcName, vals));

            }
            
            return ret;
        }

        private static int existentialConstCounter = 0;

        private List<Tuple<string, List<Model.Element>>> ExtractState(string impl, Expr expr, Model model)
        {
            var funcsUsed = FunctionCollector.Collect(expr);

            var ret = new List<Tuple<string, List<Model.Element>>>();

            foreach (var tup in funcsUsed.Where(t => t.Item2 == null))
            {
                var constant = tup.Item1;
                if (!constant2FuncCall.ContainsKey(constant.Name))
                    continue;

                var func = constant2FuncCall[constant.Name];
                var funcName = (func.Fun as FunctionCall).FunctionName;
                var vals = new List<Model.Element>();
                prover.Context.BoogieExprTranslator.Translate(func.Args).Iter(ve => vals.Add(getValue(ve, model)));
                ret.Add(Tuple.Create(funcName, vals));
            }

            foreach (var tup in funcsUsed.Where(t => t.Item2 != null))
            {
                var constant = tup.Item1;
                var boundExpr = tup.Item2;

                if (!constant2FuncCall.ContainsKey(constant.Name))
                    continue;

                // There are some bound variables (because the existential function was inside an \exists).
                // We must find an assignment for bound varibles 

                // First, peice apart the existential functions
                var cd = new Duplicator();
                var tup2 = ExistentialExprModelMassage.Massage(cd.VisitExpr(boundExpr.Body));
                var be = tup2.Item1;
                Expr env = Expr.True;
                foreach (var ahFunc in tup2.Item2)
                {
                    var tup3 = impl2FuncCalls[impl].First(t => t.Item2.Name == ahFunc.Name);
                    var varList = new List<Expr>();
                    tup3.Item3.Args.OfType<Expr>().Iter(v => varList.Add(v));

                    env = Expr.And(env, function2Value[tup3.Item1].Gamma(varList));
                }
                be = Expr.And(be, Expr.Not(env));

                // map formals to constants
                var formalToConstant = new Dictionary<string, Constant>();
                foreach (var f in boundExpr.Dummies.OfType<Variable>())
                    formalToConstant.Add(f.Name, new Constant(Token.NoToken, new TypedIdent(Token.NoToken, f.Name + "@subst@" + (existentialConstCounter++), f.TypedIdent.Type), false));
                be = Substituter.Apply(new Substitution(v => formalToConstant.ContainsKey(v.Name) ? Expr.Ident(formalToConstant[v.Name]) : Expr.Ident(v)), be);
                formalToConstant.Values.Iter(v => prover.Context.DeclareConstant(v, false, null));

                var reporter = new MLHoudiniErrorReporter();
                var ve = prover.Context.BoogieExprTranslator.Translate(be);
                prover.Assert(ve, true);
                prover.Check();
                var proverOutcome = prover.CheckOutcomeCore(reporter);
                if (proverOutcome != ProverInterface.Outcome.Invalid)
                    continue;
                model = reporter.model;

                var func = constant2FuncCall[constant.Name];
                var funcName = (func.Fun as FunctionCall).FunctionName;
                var vals = new List<Model.Element>();
                foreach (var funcArg in func.Args.OfType<Expr>())
                {
                    var arg = Substituter.Apply(new Substitution(v => formalToConstant.ContainsKey(v.Name) ? Expr.Ident(formalToConstant[v.Name]) : Expr.Ident(v)), funcArg);
                    vals.Add(getValue(prover.Context.BoogieExprTranslator.Translate(arg), model));
                }
                ret.Add(Tuple.Create(funcName, vals));

            }

            return ret;
        }

        private Model.Element getValue(VCExpr arg, Model model)
        {

            if (arg is VCExprLiteral)
            {
                //return model.GetElement(arg.ToString());
                return model.MkElement(arg.ToString());
            }

            else if (arg is VCExprVar)
            {
                var el = model.TryGetFunc(prover.Context.Lookup(arg as VCExprVar));
                if (el != null)
                {
                    Debug.Assert(el.Arity == 0 && el.AppCount == 1);
                    return el.Apps.First().Result;
                }
                else
                {
                    // Variable not defined; assign arbitrary value
                    if (arg.Type.IsBool)
                        return model.MkElement("false");
                    else if (arg.Type.IsInt)
                        return model.MkIntElement(0);
                    else
                        return null;
                }
            }
            else if (arg is VCExprNAry && (arg as VCExprNAry).Op is VCExprBvOp)
            {
                // support for BV constants
                var bvc = (arg as VCExprNAry)[0] as VCExprLiteral;
                if (bvc != null)
                {
                    var ret = model.TryMkElement(bvc.ToString() + arg.Type.ToString());
                    if (ret != null && (ret is Model.BitVector)) return ret;
                }
            }
           
            var val = prover.Evaluate(arg);
            if (val is int || val is bool || val is Microsoft.Basetypes.BigNum)
            {
                return model.MkElement(val.ToString());
            }
            else
            {
                Debug.Assert(false);
            }
            return null;
        }

        // Remove functions AbsHoudiniConstant from the expressions and substitute them with "true"
        class ExistentialExprModelMassage : StandardVisitor
        {
            List<Function> ahFuncs;

            public ExistentialExprModelMassage()
            {
                ahFuncs = new List<Function>();
            }

            public static Tuple<Expr, List<Function>> Massage(Expr expr)
            {
                var ee = new ExistentialExprModelMassage();
                expr = ee.VisitExpr(expr);
                return Tuple.Create(expr, ee.ahFuncs);
            }

            public override Expr VisitNAryExpr(NAryExpr node)
            {
                if (node.Fun is FunctionCall && (node.Fun as FunctionCall).FunctionName.StartsWith("AbsHoudiniConstant"))
                {
                    ahFuncs.Add((node.Fun as FunctionCall).Func);
                    return Expr.True;
                }

                return base.VisitNAryExpr(node);
            }
        }

        class FunctionCollector : StandardVisitor
        {
            public List<Tuple<Function, ExistsExpr>> functionsUsed;
            ExistsExpr existentialExpr;

            public FunctionCollector()
            {
                functionsUsed = new List<Tuple<Function, ExistsExpr>>();
                existentialExpr = null;
            }

            public static List<Tuple<Function, ExistsExpr>> Collect(Expr expr)
            {
                var fv = new FunctionCollector();
                fv.VisitExpr(expr);
                return fv.functionsUsed;
            }

            public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
            {
                var oldE = existentialExpr;

                if (node is ExistsExpr)
                    existentialExpr = (node as ExistsExpr);

                node = base.VisitQuantifierExpr(node);

                existentialExpr = oldE;
                return node;
            }

            public override Expr VisitNAryExpr(NAryExpr node)
            {
                if (node.Fun is FunctionCall)
                {
                    var collector = new VariableCollector();
                    collector.Visit(node);

                    if(existentialExpr != null && existentialExpr.Dummies.Intersect(collector.usedVars).Any())
                        functionsUsed.Add(Tuple.Create((node.Fun as FunctionCall).Func, existentialExpr));
                    else
                        functionsUsed.Add(Tuple.Create<Function, ExistsExpr>((node.Fun as FunctionCall).Func, null));
                }

                return base.VisitNAryExpr(node);
            }
        }

        class P_FunctionCollector : StandardVisitor
        {
            public List<Function> functionsUsed;
            
            public P_FunctionCollector()
            {
                functionsUsed = new List<Function>();
            }

            public static List<Function> Collect(Expr expr)
            {
                var fv = new P_FunctionCollector();
                fv.VisitExpr(expr);
                return fv.functionsUsed;
            }

            public override BinderExpr VisitBinderExpr(BinderExpr node)
            {
                Debug.Assert(false);
 	            return base.VisitBinderExpr(node);
            }
                 
            public override Expr VisitNAryExpr(NAryExpr node)
            {
                if (node.Fun is FunctionCall)
                {
                    var collector = new VariableCollector();
                    collector.Visit(node);

                    functionsUsed.Add((node.Fun as FunctionCall).Func);
                }

                return base.VisitNAryExpr(node);
            }
        }

        class MLHoudiniCounterexampleCollector : VerifierCallback
        {
            /*public HashSet<string> funcsChanged;            
            public int numErrors;
             */
            public string currImpl;
            public List<Counterexample> real_errors;
            public List<Counterexample> conjecture_errors;
            public List<Counterexample> implication_errors;

            MLHoudini container;

            public MLHoudiniCounterexampleCollector(MLHoudini container)
            {
                this.container = container;
                Reset(null);
            }

            public void Reset(string impl)
            {
                //funcsChanged = new HashSet<string>();
                currImpl = impl;
                //numErrors = 0;
                real_errors = new List<Counterexample>();
                conjecture_errors = new List<Counterexample>();
                implication_errors = new List<Counterexample>();
            }

            public override void OnCounterexample(Counterexample ce, string reason)
            {                
                //numErrors++;                
#if Pranav
                bool counterExampleAdded;
                if (container.HandleCounterExample(currImpl, ce, out counterExampleAdded))
                {
                    real_errors.Add(ce);
                }
                else
                {
                    if (counterExampleAdded)
                    {
                        conjecture_errors.Add(ce);
                    }
                }
#endif
                bool cexAdded;
                if (container.HandleCounterExample(currImpl, ce, out cexAdded))
                {
                    real_errors.Add(ce);
                }
                else
                {
                    if (cexAdded)
                    {
                        conjecture_errors.Add(ce);
                    }
                    else
                    {
                        implication_errors.Add(ce);
                    }
                }
                //funcsChanged.UnionWith(
                //    container.HandleCounterExample(currImpl, ce));
            }
        }

        private void GenVC(Implementation impl)
        {
            ModelViewInfo mvInfo;
            Dictionary<int, Absy> label2absy;
            var collector = new MLHoudiniCounterexampleCollector(this);
            collector.OnProgress("HdnVCGen", 0, 0, 0.0);

            if (CommandLineOptions.Clo.Trace)
            {
                Console.WriteLine("Generating VC of {0}", impl.Name);
            }

            vcgen.ConvertCFG2DAG(impl);
            var gotoCmdOrigins = vcgen.PassifyImpl(impl, out mvInfo);

            // Inline functions
            (new InlineFunctionCalls()).VisitBlockList(impl.Blocks);

            ExtractQuantifiedExprs(impl);
            StripOutermostForall(impl);

            //CommandLineOptions.Clo.PrintInstrumented = true;
            //var tt = new TokenTextWriter(Console.Out);
            //impl.Emit(tt, 0);
            //tt.Close();

            // Intercept the FunctionCalls of the existential functions, and replace them with Boolean constants
            var existentialFunctionNames = new HashSet<string>(existentialFunctions.Keys);
            var fv = new ReplaceFunctionCalls(existentialFunctionNames);
            fv.VisitBlockList(impl.Blocks);

            impl2functionsAsserted.Add(impl.Name, fv.functionsAsserted);
            impl2functionsAssumed.Add(impl.Name, fv.functionsAssumed);

            fv.functionsAssumed.Iter(f => function2implAssumed[f].Add(impl.Name));
            fv.functionsAsserted.Iter(f => function2implAsserted[f].Add(impl.Name));

            impl2FuncCalls.Add(impl.Name, fv.functionsUsed);
            fv.functionsUsed.Iter(tup => constant2FuncCall.Add(tup.Item2.Name, tup.Item3));

            HashSet<string> constantsAssumed = new HashSet<string>();
            fv.functionsUsed.Where(tup => impl2functionsAssumed[impl.Name].Contains(tup.Item1)).Iter(tup => constantsAssumed.Add(tup.Item2.Name));

            var gen = prover.VCExprGen;
            VCExpr controlFlowVariableExpr = CommandLineOptions.Clo.UseLabels ? null : gen.Integer(Microsoft.Basetypes.BigNum.ZERO);

            var vcexpr = vcgen.P_GenerateVC(impl, constantsAssumed, controlFlowVariableExpr, out label2absy, prover.Context);
            //var vcexpr = vcgen.GenerateVC(impl, controlFlowVariableExpr, out label2absy, prover.Context);

            if (!CommandLineOptions.Clo.UseLabels)
            {
                VCExpr controlFlowFunctionAppl = gen.ControlFlowFunctionApplication(gen.Integer(Microsoft.Basetypes.BigNum.ZERO), gen.Integer(Microsoft.Basetypes.BigNum.ZERO));
                VCExpr eqExpr = gen.Eq(controlFlowFunctionAppl, gen.Integer(Microsoft.Basetypes.BigNum.FromInt(impl.Blocks[0].UniqueId)));
                vcexpr = gen.Implies(eqExpr, vcexpr);
            }

            ProverInterface.ErrorHandler handler = null;
            if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Local)
                handler = new VCGen.ErrorReporterLocal(gotoCmdOrigins, label2absy, impl.Blocks, vcgen.incarnationOriginMap, collector, mvInfo, prover.Context, program);
            else
                handler = new VCGen.P_ErrorReporter(gotoCmdOrigins, label2absy, impl.Blocks, vcgen.incarnationOriginMap, collector, mvInfo, prover.Context, program, constantsAssumed);

            impl2ErrorHandler.Add(impl.Name, Tuple.Create(handler, collector));

            //Console.WriteLine("VC of {0}: {1}", impl.Name, vcexpr);

            // Create a macro so that the VC can sit with the theorem prover
            Macro macro = new Macro(Token.NoToken, impl.Name + "Macro", new List<Variable>(), new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Bpl.Type.Bool), false));
            prover.DefineMacro(macro, vcexpr);

            //Console.WriteLine("Function " + impl.Name + ":\n" + vcexpr.ToString());

            // Store VC
            impl2VC.Add(impl.Name, gen.Function(macro));

            // HACK: push the definitions of constants involved in function calls
            // It is possible that some constants only appear in function calls. Thus, when
            // they are replaced by Boolean constants, it is possible that (get-value) will 
            // fail if the expression involves such constants. All we need to do is make sure
            // these constants are declared, because otherwise, semantically we are doing
            // the right thing.
            foreach (var tup in fv.functionsUsed)
            {
                // Ignore ones with bound varibles
                if (tup.Item2.InParams.Count > 0) continue;
                var tt = prover.Context.BoogieExprTranslator.Translate(tup.Item3);
                tt = prover.VCExprGen.Or(VCExpressionGenerator.True, tt);
                prover.Assert(tt, true);
            }
        }

        // convert "foo(... forall e ...) to:
        //    (p iff forall e) ==> foo(... p ...) 
        // where p is a fresh boolean variable and foo is an existential constant
        private void ExtractQuantifiedExprs(Implementation impl)
        {
            var funcs = new HashSet<string>(existentialFunctions.Keys);
            foreach (var blk in impl.Blocks)
            {
                foreach (var acmd in blk.Cmds.OfType<AssertCmd>())
                {
                    var ret = ExtractQuantifiers.Extract(acmd.Expr, funcs);
                    acmd.Expr = ret.Item1;
                    impl.LocVars.AddRange(ret.Item2);
                }
            }
        }

        // convert "assert e1 && forall x: e2" to
        //    assert e1 && e2[x <- x@bound]
        private void StripOutermostForall(Implementation impl)
        {
            var funcs = new HashSet<string>(existentialFunctions.Keys);
            foreach (var blk in impl.Blocks)
            {
                foreach (var acmd in blk.Cmds.OfType<AssertCmd>())
                {
                    var ret = StripQuantifiers.Run(acmd.Expr, funcs);
                    acmd.Expr = ret.Item1;
                    impl.LocVars.AddRange(ret.Item2);
                }
            }
        }

        private void Inline()
        {
            if (CommandLineOptions.Clo.InlineDepth < 0)
                return;

            var callGraph = BuildCallGraph();

            foreach (Implementation impl in callGraph.Nodes)
            {
                InlineRequiresVisitor inlineRequiresVisitor = new InlineRequiresVisitor();
                inlineRequiresVisitor.Visit(impl);
            }

            foreach (Implementation impl in callGraph.Nodes)
            {
                FreeRequiresVisitor freeRequiresVisitor = new FreeRequiresVisitor();
                freeRequiresVisitor.Visit(impl);
            }

            foreach (Implementation impl in callGraph.Nodes)
            {
                InlineEnsuresVisitor inlineEnsuresVisitor = new InlineEnsuresVisitor();
                inlineEnsuresVisitor.Visit(impl);
            }

            foreach (Implementation impl in callGraph.Nodes)
            {
                impl.OriginalBlocks = impl.Blocks;
                impl.OriginalLocVars = impl.LocVars;
            }
            foreach (Implementation impl in callGraph.Nodes)
            {
                CommandLineOptions.Inlining savedOption = CommandLineOptions.Clo.ProcedureInlining;
                CommandLineOptions.Clo.ProcedureInlining = CommandLineOptions.Inlining.Spec;
                Inliner.ProcessImplementationForHoudini(program, impl);
                CommandLineOptions.Clo.ProcedureInlining = savedOption;
            }
            foreach (Implementation impl in callGraph.Nodes)
            {
                impl.OriginalBlocks = null;
                impl.OriginalLocVars = null;
            }

            Graph<Implementation> oldCallGraph = callGraph;
            callGraph = new Graph<Implementation>();
            foreach (Implementation impl in oldCallGraph.Nodes)
            {
                callGraph.AddSource(impl);
            }
            foreach (Tuple<Implementation, Implementation> edge in oldCallGraph.Edges)
            {
                callGraph.AddEdge(edge.Item1, edge.Item2);
            }
            int count = CommandLineOptions.Clo.InlineDepth;
            while (count > 0)
            {
                foreach (Implementation impl in oldCallGraph.Nodes)
                {
                    List<Implementation> newNodes = new List<Implementation>();
                    foreach (Implementation succ in callGraph.Successors(impl))
                    {
                        newNodes.AddRange(oldCallGraph.Successors(succ));
                    }
                    foreach (Implementation newNode in newNodes)
                    {
                        callGraph.AddEdge(impl, newNode);
                    }
                }
                count--;
            }
        }

        private Graph<Implementation> BuildCallGraph()
        {
            Graph<Implementation> callGraph = new Graph<Implementation>();
            Dictionary<Procedure, HashSet<Implementation>> procToImpls = new Dictionary<Procedure, HashSet<Implementation>>();
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Procedure proc = decl as Procedure;
                if (proc == null) continue;
                procToImpls[proc] = new HashSet<Implementation>();
            }
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl == null || impl.SkipVerification) continue;
                callGraph.AddSource(impl);
                procToImpls[impl.Proc].Add(impl);
            }
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl == null || impl.SkipVerification) continue;
                foreach (Block b in impl.Blocks)
                {
                    foreach (Cmd c in b.Cmds)
                    {
                        CallCmd cc = c as CallCmd;
                        if (cc == null) continue;
                        foreach (Implementation callee in procToImpls[cc.Proc])
                        {
                            callGraph.AddEdge(impl, callee);
                        }
                    }
                }
            }
            return callGraph;
        }
    }   

    public interface MLICEDomain
    {
        bool constructModel(string funcName, TreeNode root, Dictionary<string, Dictionary<string, Expr>> attr2Expr, Dictionary<string, int> functionID);  // returns whether the abstract value has changed?
        Expr Gamma(List<Expr> vars);
        //bool TypeCheck(List<Type> argTypes, out string msg);     
    }   


    /*
    class InlineFunctionCalls : StandardVisitor
    {
        public Stack<string> inlinedFunctionsStack;

        public InlineFunctionCalls()
        {
            inlinedFunctionsStack = new Stack<string>();
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            var fc = node.Fun as FunctionCall;
            if (fc != null && fc.Func.Body != null && QKeyValue.FindBoolAttribute(fc.Func.Attributes, "inline"))
            {
                if (inlinedFunctionsStack.Contains(fc.Func.Name))
                {
                    // recursion detected
                    throw new MLHoudiniInternalError("Recursion detected in function declarations");
                }

                // create a substitution
                var subst = new Dictionary<Variable, Expr>();
                for (int i = 0; i < node.Args.Count; i++)
                {
                    subst.Add(fc.Func.InParams[i], node.Args[i]);
                }

                var e =
                    Substituter.Apply(new Substitution(v => subst.ContainsKey(v) ? subst[v] : Expr.Ident(v)), fc.Func.Body);

                inlinedFunctionsStack.Push(fc.Func.Name);

                e = base.VisitExpr(e);

                inlinedFunctionsStack.Pop();

                return e;
            }
            return base.VisitNAryExpr(node);
        }
    }
     */
 
    public class MLHoudiniInternalError : System.ApplicationException
    {
        public MLHoudiniInternalError(string msg) : base(msg) { }

    };


    class InlineFunctionCalls : StandardVisitor
    {
        public Stack<string> inlinedFunctionsStack;

        public InlineFunctionCalls()
        {
            inlinedFunctionsStack = new Stack<string>();
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            var fc = node.Fun as FunctionCall;
            if (fc != null && fc.Func.Body != null && QKeyValue.FindBoolAttribute(fc.Func.Attributes, "inline"))
            {
                if (inlinedFunctionsStack.Contains(fc.Func.Name))
                {
                    // recursion detected
                    throw new MLHoudiniInternalError("Recursion detected in function declarations");
                }

                // create a substitution
                var subst = new Dictionary<Variable, Expr>();
                for (int i = 0; i < node.Args.Count; i++)
                {
                    subst.Add(fc.Func.InParams[i], node.Args[i]);
                }

                var e =
                    Substituter.Apply(new Substitution(v => subst.ContainsKey(v) ? subst[v] : Expr.Ident(v)), fc.Func.Body);

                inlinedFunctionsStack.Push(fc.Func.Name);

                e = base.VisitExpr(e);

                inlinedFunctionsStack.Pop();

                return e;
            }
            return base.VisitNAryExpr(node);
        }
    }
 
    
    class MLHoudiniErrorReporter : ProverInterface.ErrorHandler
    {
        public Model model;

        public MLHoudiniErrorReporter()
        {
            model = null;
        }

        public override void OnModel(IList<string> labels, Model model)
        {
            Debug.Assert(model != null);
            if(CommandLineOptions.Clo.PrintErrorModel >= 1) model.Write(Console.Out);
            this.model = model;
        }
    }

}
