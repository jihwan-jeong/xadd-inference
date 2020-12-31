package camdp;

// Packages to import

import graph.Graph;

import java.io.*;
import java.util.*;

import java.math.BigDecimal;
import java.text.DecimalFormat;

import util.IntTriple;
import xadd.XADD;
import xadd.XADDUtils;
import xadd.ExprLib.*;
import xadd.XADD.*;

/**
 * Main Continuous State and Action MDP (CAMDP) dynamic programming solution class
 * (handles discrete actions, continuous actions, and continuous noise)
 *
 * @author Zahra Zamani
 * @author Scott Sanner
 * @version 1.0
 * @language Java (JDK 1.5)
 * <p/>
 * TODO: Reintroduce policy annotation
 * TODO: Allow alternate initialization of V^0 in input file
 * TODO: Action and next-state dependent reward expectations can be pre-computed and added
 * in after value function regression but before continuous parameter maximization.
 */
public class CAMDP {

    /* Constants */
    public final static int MAXIMUM_ITER = 10000;
    public final static String RESULTS_DIR = "results"; // Diagnostic output destination

    // Display Flags
    public final static boolean DISPLAY_PREMAX_Q = false;
    public final static boolean DISPLAY_POSTMAX_Q = false;
    public final static boolean DISPLAY_V = true;
    public final static boolean DISPLAY_MAX = false;
    private static final boolean SILENT_PLOT = true;
    private static final boolean DONT_SHOW_HUGE_GRAPHS = true;
    private static final int MAXIMUM_XADD_DISPLAY_SIZE = 500;
    public static final boolean SILENCE_ERRORS_PLOTS = false;
    
    //Prune and Linear Flags
    public double maxImediateReward;
    public boolean LINEAR_PROBLEM = true;
    public boolean CONTINUOUS_ACTIONS = true;
    public boolean APPROX_PRUNING = false;
    public double APPROX_ERROR = 0.0d;
    public boolean APPROX_ALWAYS = false;
    public boolean COMPARE_OPTIMAL = false;
    public boolean DISCRETIZE_PROBLEM = false;
    public int DISCRETE_NUMBER = 11;
    public int GLOBAL_LB = -9;
    public int GLOBAL_UB = 9;

    //Optimal solution maintenance
    public Integer optimalHorizon;
    public ArrayList<Integer> optimalDDList = new ArrayList<Integer>();
    public ArrayList<Double> optimalMaxValueList = new ArrayList<Double>();

    /* Maintain an explicit policy? */
    public final static boolean MAINTAIN_POLICY = false;

    /* Cache maintenance */
    // Unused FLAG? public final static boolean ALWAYS_FLUSH = false; // Always flush DD caches?
    public final static double FLUSH_PERCENT_MINIMUM = 0.3d; // Won't flush until < amt

    /* For printing */
    public static DecimalFormat _df = new DecimalFormat("#.########");
    public PrintStream _logStream = null;
    public PrintStream _testLogStream = null;

    /* Static variables */
    public static long _lTime; // For timing purposes
    public static Runtime RUNTIME = Runtime.getRuntime();
    public final static int nTimers = 8;
    public static long[] _lTimers = new long[nTimers];
    private static final boolean EFFICIENCY_DEBUG = false;
    public static String _domain;

    /* Local vars */
    public boolean DISPLAY_2D = false;
    public boolean DISPLAY_3D = true;

    public String _problemFile = null;
    public String _logFileRoot = null;
    public XADD _context = null;
    public HashSet<String> _hsBoolSVars;
    public HashSet<String> _hsContSVars;
    public HashSet<String> _hsBoolIVars;
    public HashSet<String> _hsContIVars;
    public HashSet<String> _hsContAVars;
    public HashSet<String> _hsContLPVars;

    public HashSet<String> _hsNoiseVars;

    public HashSet<String> _hsBoolNSVars; // Next state vars
    public HashSet<String> _hsContNSVars; // Next state vars

    public HashSet<String> _hsBoolAllVars; // Retain order given in MDP file
    public HashSet<String> _hsContAllVars; // Retain order given in MDP file

    public Integer _valueDD; // The resulting value function once this CMDP has
    public Integer _maxDD;
    public Integer _prevDD;
    public BigDecimal _bdDiscount; // Discount (gamma) for CMDP
    public Integer _nMaxIter;   // Number of iterations for CMDP
    public Integer _nCurIter;   // Number of iterations for CMDP

    public HashMap<String, ArithExpr> _hmPrimeSubs;
    public HashMap<String, CAction> _hmName2Action;
    public HashMap<IntTriple, Integer> _hmContRegrCache;
    public HashMap<Decision, Boolean> _hmDomainConstraint;
    public HashMap<Decision, Boolean> _hmDomainConstraintRain;
    public HashMap<String, Integer> _hmVar2EqConst;

    // Constraints not currently allowed, should be applied to the reward as -Infinity
    //public ArrayList<Integer>         _alConstraints;
    public String _probSize;
    public ComputeQFunction _qfunHelper = null;

    public State _initialS = null;

    // Map for setting up actions in reservoir problem
    HashMap<String, String> _action2Var = new HashMap<String, String>();
    
    // Map for setting up actions in bandwidth optimization problem
    HashMap<String, List<String>> _action2Links = new HashMap<String, List<String>>();

    ////////////////////////////////////////////////////////////////////////////
    // Constructors
    ////////////////////////////////////////////////////////////////////////////

    /**
     * Constructor - filename
     */
    public CAMDP(String filename) {
        this(filename, HierarchicalParser.ParseFile(filename));
    }

    /**
     * Constructor - pre-parsed file
     */
    private CAMDP(String file_source, ArrayList input) {

        // Basic initializations
        _problemFile = file_source;
        _logFileRoot = insertDirectory(_problemFile, RESULTS_DIR);
        _context = new XADD();
        _prevDD = _maxDD = _valueDD = null;
        _bdDiscount = new BigDecimal("" + (-1));
        _nMaxIter = null;
        _hmName2Action = new HashMap<String, CAction>();
        _hmDomainConstraint = new HashMap<Decision, Boolean>();
        _hmDomainConstraintRain = new HashMap<Decision, Boolean>();

        // Setup CAMDP according to parsed file contents
        readBandwidthDomain(file_source);
        setDomain(file_source);
        ParseCAMDP parser = new ParseCAMDP(this);
        parser.buildCAMDP(input);
        _context.addContinuousVarsBounds(parser._minCVal, parser._maxCVal);
        //_alConstraints = parser.getConstraints();
        _nMaxIter = parser.getIterations();
        _bdDiscount = parser.getDiscount();
        _hmName2Action = parser.getHashmap();
        _hmContRegrCache = new HashMap<IntTriple, Integer>();

        // Setup variable sets and lists
        _hsBoolSVars = new HashSet<String>(intern(parser.getBVars()));
        _hsContSVars = new HashSet<String>(intern(parser.getCVars()));
        _hsBoolIVars = new HashSet<String>(intern(parser.getIBVars()));
        _hsContIVars = new HashSet<String>(intern(parser.getICVars()));
        _hsContAVars = new HashSet<String>(intern(parser.getAVars()));
        _hsNoiseVars = new HashSet<String>(intern(parser.getNoiseVars()));
        _hsContLPVars = new HashSet<String>(intern(parser.getLPVars()));

        _hsBoolAllVars = new HashSet<String>(_hsBoolSVars);
        _hsBoolAllVars.addAll(_hsBoolIVars);
        _hsContAllVars = new HashSet<String>(_hsContSVars);
        _hsContAllVars.addAll(_hsContAVars);
        _hsContAllVars.addAll(_hsContIVars);
        //_context._hmContinuousVars = _alContAllVars;
        // Build cur-state var -> next-state var map
        _hsBoolNSVars = new HashSet<String>();
        _hsContNSVars = new HashSet<String>();
        _hmPrimeSubs = new HashMap<String, ArithExpr>();
        _hmVar2EqConst = new HashMap<String, Integer>();

        for (String var : _hsContSVars) {
            String prime_var = var + "'";
            _hmPrimeSubs.put(var, new VarExpr(prime_var));
            _hsContNSVars.add(prime_var);
        }
        for (String var : _hsBoolSVars) {
            String prime_var = var + "'";
            _hmPrimeSubs.put(var, new VarExpr(prime_var));
            _hsBoolNSVars.add(prime_var);
        }

        CONTINUOUS_ACTIONS = _hsContAVars.isEmpty()? false: true;
        LINEAR_PROBLEM = parser.LINEARITY;
        maxImediateReward = parser.MAXREWARD;
        
        // solve the transition LP
        int lp0 = _context._lp0;
        int lp1 = _context._lp1;
        // traffic and bandwidth examples
        if (lp0 != -1 && lp1 == -1){
            if (_domain != "reservoir"){
                argmaxLPandModifyActionTransitions(lp0, parser);
            } else {
                System.out.println("Wrong domain file given. Check " + file_source);
                System.exit(1);
            }
        // reservoir example
        } else if (lp0 != -1 && lp1 != -1){
            argmaxLPandModifyActionTransitions(lp0, lp1, parser);
        }

        // This helper class performs the regression
        _qfunHelper = new ComputeQFunction(_context, this);
        if ( !parser.get_initBVal().isEmpty() || !parser.get_initCVal().isEmpty() )_initialS = new State(parser.get_initCVal(), parser.get_initBVal());

        // Setup a logger
        try {
            _logStream = new PrintStream(new FileOutputStream(/*"timeSpace.txt"));*/_logFileRoot + ".log"));
            _logStream.println(this.toString());
            //Default log to stdout
            _testLogStream = System.out;
        } catch (FileNotFoundException e) {
            System.err.println(e);
            e.printStackTrace();
            System.exit(1);
        }
                
        // Flush caches after getting the argmax
        flushCaches(true);
    }

    public void setDomain(String filename){
        if (filename.contains("traffic")){
            _domain = "traffic";
        } else if (filename.contains("reservoir")){
            _domain = "reservoir";
        } else if (filename.contains("bandopt")){
            _domain = "bandwidth";
        } else {
            System.out.println("Unrecognized domain... Exiting...");
            System.exit(1);
        }
        _context._domain = _domain;
    }

    private void readBandwidthDomain(String file_source){
        if (file_source.contains("Bandwidth")){
            String[] tempStr = file_source.split("\\.")[0].split("/");
            int fnameLength = tempStr[tempStr.length-1].length();
            _probSize = Character.toString(tempStr[tempStr.length-1].charAt(fnameLength-1));
            File fname = new File(String.format("src/camdp/ex/discact/BandwidthOptimizationProblems/resources/links%s.txt", _probSize));
            // System.out.println(links_file.getAbsolutePath());
            try {
                FileReader fr = new FileReader(fname);
                BufferedReader reader = new BufferedReader(fr);
                while (true) {
                    String line = reader.readLine();
                    if (line == null) break;
    
                    String[] path2Links = line.split(":");
                    String actionPath = path2Links[0].trim();
                    String[] links = path2Links[1].trim().split("\\s*,\\s*");
                    List<String> listLinks = Arrays.asList(links);
                    _action2Links.put(actionPath, listLinks);
                }
            } catch (IOException e1) {
                // TODO Auto-generated catch block
                e1.printStackTrace();
            }
        }
    }

    private void argmaxLPandModifyActionTransitions(Integer lp, ParseCAMDP parser) {
        /**
         * Perform argmax over the LP.
         * Substitute argmax results over transition equations in _hmName2Action.
         * This method works for the traffic and the bandwidth example. 
         */
        HashSet<String> optSet = new HashSet<String>();
        HashSet<String> actIVarSet = new HashSet<String>();
        boolean isMax = true;
        ArrayList<String> varOrder = new ArrayList<String>();
        Integer dd = lp;

        // Handle equality constraints if exist
        for (Map.Entry<String, ArrayList> eqconst : parser._eqConst.entrySet()){
            String var = eqconst.getKey();
            Integer eq_rhs = _context.buildCanonicalXADD(eqconst.getValue());
            _hmVar2EqConst.put(var, eq_rhs);                

            // Now, substitute rhs to the LP XADD wherever it appears
            dd = _context.reduceProcessXADDLeaf(eq_rhs, _context.new DeltaFunctionSubstitution(var, dd), true);
        }        

        // Get a set of all variables and sequentially max out while keeping track of the annotations
        HashSet<String> varSet = _context.collectVars(dd);
        for (String var: parser._objVar){
            varOrder.add(var);              // Max out variables in the objective function first
        }

        // Max out the lp
        for (String var: varSet) {
            if (!_hsContLPVars.contains(var) && !_hsContSVars.contains(var)){
                actIVarSet.add(var);
            } else if (_hsContLPVars.contains(var) && !varOrder.contains(var)){
                varOrder.add(var);      // variables not in the objective are maximized at the end
            }
        }

        for (String var: varOrder){
            optSet.add(var);
            double min_val = parser._minCVal.get(var);
            double max_val = parser._maxCVal.get(var);

            XADDLeafMinOrMax max = _context.new XADDLeafMinOrMax(var, min_val, max_val, isMax, System.out);
            _context.setCurrOptVar(var);
            _context.reduceProcessXADDLeaf(dd, max, false);

            // Store argmax xadd to a hash map
            dd = max._runningResult;
            Integer anno = -1;
            if (!parser._objVar.contains(var)){     // Ignore this part.. doing nothing special, but left as is just as a note
                anno = _context.getArg(dd, var);
            } else {
                anno = _context.getArg(dd);
            }
            anno = _context.reduceLinearize(anno);
            anno = _context.reduceLP(anno);

            _context._hmVar2Anno.put(var, anno);
        }
        
        // Compute the argmax xadd of all variables
        _context.argMax(varOrder);

        // Print out argmax solution for each action
        double[][] actionLink = new double[][] {{1, 0, 0, 1, 0}, {1, 0, 1, 0, 1}, {0, 1, 0, 0, 1}, 
                                          {1, 0, 1, 1, 1}, {1, 1, 0, 1, 1}, {1, 1, 1, 0, 1}, {1, 1, 1, 1, 1}};
        String[] links = new String[] {"ao1", "ao2", "a12", "a1e", "a2e"};
        String[] actionString = new String[] {"path1", "path2", "path3", "path12", "path13", "path23", "path123"};
        
        int k = 0;
        for (double[] act : actionLink){    
            System.out.println(String.format("Action: %s", actionString[k]));
            for (String v : varOrder){
                Integer anno = _context._hmVar2Anno.get(v);
                
                Integer anno_evaluated = substituteForEvaluation(anno, links, act);
                System.out.println(String.format("\tvar: %s\tvalue: %s", v, _context.getString(anno_evaluated)));
            }
            k++;
        }

        // Integer obj = _context.apply(_context._hmVar2Anno.get("dq2"), _context._hmVar2Anno.get("dq3"), _context.SUM);
        // display3D(obj, "Objective (q1=15)");

        // Now, for each action, modify argmax XADD of dq variables and substitute into transition & reward XADDs.
        // Reward and transition are referred by _reward and _hmVar2DD, respectively.
        for (Map.Entry<String, CAction> aname2CAction : _hmName2Action.entrySet()){
            String aname = aname2CAction.getKey();
            CAction act = aname2CAction.getValue();
            Integer origR = act._reward;
            Integer modifiedR = origR;
            HashMap<String, Integer> origTrans = act._hmVar2DD;
            HashMap<String, Integer> modifiedTrans = new HashMap<String, Integer>();
            HashMap<String, ArithExpr> aReplace = new HashMap<String, ArithExpr>();

            // If actIVar exists.. (skipped in the traffic example)
            for (String actVar : actIVarSet){
                List<String> a_1s = _action2Links.get(aname);
                if (a_1s.contains(actVar)){
                    aReplace.put(actVar, new DoubleExpr(1.0));
                } else {
                    aReplace.put(actVar, new DoubleExpr(0.0));
                }
            }

            // Substitute actVar values to Reward
            if (!aReplace.isEmpty()){
                modifiedR = _context.substitute(origR, aReplace);
                modifiedR = _context.reduceLP(_context.reduceLinearize(modifiedR));
            }

            // Substitute actVar values to argmax XADD of each variable subject to LP optimization.
            // Then, substitute those into reward and transition XADDs.
            HashMap<String, Integer> hmVar2ModifiedOptVar = new HashMap<String, Integer>();
            for (String optVar : optSet){   
                Integer origVar = _context._hmVar2Anno.get(optVar);
                Integer modifiedOptVar = origVar;
                if (!aReplace.isEmpty()){
                    modifiedOptVar = _context.substitute(origVar, aReplace);    
                    modifiedOptVar = _context.reduceLP(_context.reduceLinearize(modifiedOptVar));
                }

                // Handle equality constraints
                for (Map.Entry<String, Integer> eqConst : _hmVar2EqConst.entrySet()){
                    String eqOptVar = eqConst.getKey();
                    Integer eqRhs = eqConst.getValue();
                    modifiedR = _context.reduceProcessXADDLeaf(eqRhs, _context.new DeltaFunctionSubstitution(eqOptVar, modifiedR), true);
                }

                modifiedR = _context.reduceProcessXADDLeaf(modifiedOptVar, _context.new DeltaFunctionSubstitution(optVar, modifiedR), true);
                modifiedR = _context.reduceLP(_context.reduceLinearize(modifiedR));
                hmVar2ModifiedOptVar.put(optVar, modifiedOptVar);
            }

            // Substitute into transition functions
            for (Map.Entry<String, Integer> trans : origTrans.entrySet()){
                String nsVar = trans.getKey();
                Integer modifiedTfunc = trans.getValue();
                if (!aReplace.isEmpty()){
                    modifiedTfunc = _context.substitute(modifiedTfunc, aReplace);
                    modifiedTfunc = _context.reduceLP(_context.reduceLinearize(modifiedTfunc));
                } 
                
                // Handle equality constraints
                for (Map.Entry<String, Integer> eqConst : _hmVar2EqConst.entrySet()){
                    String eqOptVar = eqConst.getKey();
                    Integer eqRhs = eqConst.getValue();
                    modifiedTfunc = _context.reduceProcessXADDLeaf(eqRhs, _context.new DeltaFunctionSubstitution(eqOptVar, modifiedTfunc), true);
                }

                for (Map.Entry<String, Integer> optVar2DD : hmVar2ModifiedOptVar.entrySet()){
                    String optVar = optVar2DD.getKey();
                    Integer modifiedOptVar = optVar2DD.getValue();
                    modifiedTfunc = _context.reduceProcessXADDLeaf(modifiedOptVar, _context.new DeltaFunctionSubstitution(optVar, modifiedTfunc), true);
                    modifiedTfunc = _context.reduceLP(_context.reduceLinearize(modifiedTfunc));
                }
                modifiedTrans.put(nsVar, modifiedTfunc);
            }
            act._reward = modifiedR;
            act._hmVar2DD = modifiedTrans;

        }
    }

    private void argmaxLPandModifyActionTransitions(Integer lp0, Integer lp1, ParseCAMDP parser) {
        /**
         * Perform argmax over the LP.
         * Substitute argmax results over transition equations in _hmName2Action.
         * This method is solely for the reservoir example. 
         */
        HashSet<String> optSet = new HashSet<String>();
        HashSet<String> actIVarSet = new HashSet<String>();
        boolean isMax = true;
        ArrayList<String> varOrder0 = new ArrayList<String>();
        ArrayList<String> varOrder1 = new ArrayList<String>();
        Integer dd0 = lp0;
        Integer dd1 = lp1;
        
        // Set up domain constraints
        VarExpr l1 = new VarExpr("l1");
        VarExpr l2 = new VarExpr("l2");
        ExprDec l1_lb = _context.new ExprDec(new CompExpr(CompOperation.GT_EQ, l1, new DoubleExpr(1000.0 / 0.98)));
        ExprDec l1_ub = _context.new ExprDec(new CompExpr(CompOperation.LT_EQ, l1, new DoubleExpr(3000.0 / 0.98)));
        ExprDec l2_lb = _context.new ExprDec(new CompExpr(CompOperation.GT_EQ, l2, new DoubleExpr(700.0/0.98)));
        ExprDec l2_ub = _context.new ExprDec(new CompExpr(CompOperation.LT_EQ, l2, new DoubleExpr(2000.0/0.98)));
        _hmDomainConstraint.put(l1_lb.makeCanonical(), (Boolean) true);
        _hmDomainConstraint.put(l1_ub.makeCanonical(), (Boolean) true);
        _hmDomainConstraint.put(l2_lb.makeCanonical(), (Boolean) true);
        _hmDomainConstraint.put(l2_ub.makeCanonical(), (Boolean) true);
        ExprDec l1_lb_r = _context.new ExprDec(new CompExpr(CompOperation.GT_EQ, l1, new DoubleExpr((1000.0 - 200) / 0.98)));
        ExprDec l1_ub_r = _context.new ExprDec(new CompExpr(CompOperation.LT_EQ, l1, new DoubleExpr((3000.0 - 200) / 0.98)));
        ExprDec l2_lb_r = _context.new ExprDec(new CompExpr(CompOperation.GT_EQ, l2, new DoubleExpr((700.0 - 200) / 0.98)));
        ExprDec l2_ub_r = _context.new ExprDec(new CompExpr(CompOperation.LT_EQ, l2, new DoubleExpr((2000.0 - 200) / 0.98)));
        _hmDomainConstraintRain.put(l1_lb_r.makeCanonical(), (Boolean) true);
        _hmDomainConstraintRain.put(l1_ub_r.makeCanonical(), (Boolean) true);
        _hmDomainConstraintRain.put(l2_lb_r.makeCanonical(), (Boolean) true);
        _hmDomainConstraintRain.put(l2_ub_r.makeCanonical(), (Boolean) true);

        // Get a set of all variables and sequentially max out while keeping track of the annotations
        HashSet<String> varSet0 = _context.collectVars(dd0);
        HashSet<String> varSet1 = _context.collectVars(dd1);

        for (String var: parser._objVar){
            if (var.contains("r")) varOrder1.add(var);
            else varOrder0.add(var);
        }

        // Max out the first lp (no rain, q1 q2)
        // variables: l1, l2, q1, q2, a
        for (String var: varSet0) {
            if (!_hsContLPVars.contains(var) && !_hsContSVars.contains(var)){
                actIVarSet.add(var);
            } else if (_hsContLPVars.contains(var) && !varOrder0.contains(var)){
                varOrder0.add(var);      // variables not in the objective are maximized at the end
            }
        }
        for (String var: varOrder0){
            optSet.add(var);
            double min_val = parser._minCVal.get(var);
            double max_val = parser._maxCVal.get(var);

            XADDLeafMinOrMax max = _context.new XADDLeafMinOrMax(var, min_val, max_val, isMax, System.out);
            _context.setCurrOptVar(var);
            _context.reduceProcessXADDLeaf(dd0, max, false);

            // Store argmax xadd to a hash map
            dd0 = max._runningResult;
            Integer anno = -1;
            if (!parser._objVar.contains(var)){
                anno = _context.getArg(dd0, var);
            } else {
                anno = _context.getArg(dd0);
            }
            anno = _context.reduceLinearize(anno);
            anno = _context.reduceLP(anno);

            _context._hmVar2Anno.put(var, anno);
        }

        // Compute the argmax xadd of all variables
        _context.argMax(varOrder0);

        // Max out the second lp (rain, q1r q2r)
        // variables: l1, l2, q1r, q2r, a
        for (String var: varSet1) {
            if (!_hsContLPVars.contains(var) && !_hsContSVars.contains(var)){
                actIVarSet.add(var);
            } else if (_hsContLPVars.contains(var) && !varOrder0.contains(var)){
                varOrder1.add(var);      // variables not in the objective are maximized at the end
            }
        }

        for (String var: varOrder1){
            optSet.add(var);
            double min_val = parser._minCVal.get(var);
            double max_val = parser._maxCVal.get(var);

            XADDLeafMinOrMax max = _context.new XADDLeafMinOrMax(var, min_val, max_val, isMax, System.out);
            _context.setCurrOptVar(var);
            _context.reduceProcessXADDLeaf(dd1, max, false);

            // Store argmax xadd to a hash map
            dd1 = max._runningResult;
            Integer anno = -1;
            if (!parser._objVar.contains(var)){
                anno = _context.getArg(dd1, var);
            } else {
                anno = _context.getArg(dd1);
            }
            anno = _context.reduceLinearize(anno);
            anno = _context.reduceLP(anno);

            _context._hmVar2Anno.put(var, anno);
        }

        // Compute the argmax xadd of all variables
        HashMap<String, Integer> argmax = _context.argMax(varOrder1);

        // Print out argmax solution for each action
        // TODO

        // Now, for each action, modify argmax XADD of dq variables and substitute into transition & reward XADDs.
        // Reward and transition are referred by _reward and _hmVar2DD, respectively.
        for (Map.Entry<String, CAction> aname2CAction : _hmName2Action.entrySet()){
            String aname = aname2CAction.getKey();
            CAction act = aname2CAction.getValue();
            Integer origR = act._reward;
            Integer modifiedR = origR;
            HashMap<String, Integer> origTrans = act._hmVar2DD;
            HashMap<String, Integer> modifiedTrans = new HashMap<String, Integer>();
            HashMap<String, ArithExpr> aReplace = new HashMap<String, ArithExpr>();

            if (aname.substring(1, 2).equals("1")){
                aReplace.put("a", new DoubleExpr(1.0));
            } else {
                aReplace.put("a", new DoubleExpr(0.0));
            }

            // Substitute 'a' values to argmax XADD of each q, qr variable
            // Then, substitute those into reward and transition XADDs.
            HashMap<String, Integer> hmVar2ModifiedOptVar = new HashMap<String, Integer>();
            for (String optVar : optSet){   
                Integer origVar = _context._hmVar2Anno.get(optVar);
                Integer modifiedOptVar = _context.substitute(origVar, aReplace);
                modifiedOptVar = _context.reduceLP(_context.reduceLinearize(modifiedOptVar));
                modifiedR = _context.reduceProcessXADDLeaf(modifiedOptVar, _context.new DeltaFunctionSubstitution(optVar, modifiedR), true);
                modifiedR = _context.reduceLP(_context.reduceLinearize(modifiedR));
                hmVar2ModifiedOptVar.put(optVar, modifiedOptVar);
            }

            // Substitute into transition functions
            for (Map.Entry<String, Integer> trans : origTrans.entrySet()){
                String nsVar = trans.getKey();
                Integer modifiedTfunc = _context.substitute(trans.getValue(), aReplace);
                modifiedTfunc = _context.reduceLP(_context.reduceLinearize(modifiedTfunc));

                for (Map.Entry<String, Integer> optVar2DD : hmVar2ModifiedOptVar.entrySet()){
                    String optVar = optVar2DD.getKey();
                    Integer modifiedOptVar = optVar2DD.getValue();
                    modifiedTfunc = _context.reduceProcessXADDLeaf(modifiedOptVar, _context.new DeltaFunctionSubstitution(optVar, modifiedTfunc), true);
                    modifiedTfunc = _context.reduceLP(_context.reduceLinearize(modifiedTfunc));
                }
                modifiedTrans.put(nsVar, modifiedTfunc);
            }
            act._reward = modifiedR; //_context.getINodeCanon(r_node._var, r_low, r_high);

            act._hmVar2DD = modifiedTrans;

            // Remove unused variables (a, q1, q2, q1r, q2r)
            String[] to_remove = new String[] {"a", "q1", "q2", "q1r", "q2r"};
            for (String _v_remove : to_remove){
                act._contIntermVars.remove(_v_remove);
            }

            System.out.println("Action: " + aname + ":");
            for (String q : Arrays.copyOfRange(to_remove, 1, to_remove.length)){
                int q_xadd = hmVar2ModifiedOptVar.get(q);
                System.out.println("Original q XADD...\n" + q + ":\n" + _context.getString(q_xadd) + "\n");
                // System.out.println("Enforcing domain constraints over q variables...\n");
                // HashMap<Decision, Boolean> domainConstraint = q.contains("r")? _hmDomainConstraintRain : _hmDomainConstraint;
                // q_xadd = enforceDomainConstraint(domainConstraint, q_xadd, 0);
                // System.out.println("Modified q XADD...\n" + q + ":\n" + _context.getString(q_xadd) + "\n");
            }
            // When a = 1, plot 3D surface plot of q1, q2, q1r, q2r 
            // if (aname.equals("a1")){
            //     display3D(hmVar2modifiedOptVar.get("q1"), "q1", "src/camdp/ex/optimizedTransitions/reservoir_jihwan_q1.cmdp");
            //     display3D(hmVar2modifiedOptVar.get("q1r"), "q1r", "src/camdp/ex/optimizedTransitions/reservoir_jihwan_q1r.cmdp");
            //     display3D(hmVar2modifiedOptVar.get("q2"), "q2", "src/camdp/ex/optimizedTransitions/reservoir_jihwan_q2.cmdp");
            //     display3D(hmVar2modifiedOptVar.get("q2r"), "q2r", "src/camdp/ex/optimizedTransitions/reservoir_jihwan_q2r.cmdp");
            // }
            
            for (String optVar : optSet){
                int q_xadd = hmVar2ModifiedOptVar.get(optVar);
                display3D(q_xadd, optVar + " ("+aname+")");
            }
        }

        // Remove unused variables (a, q1, q2, q1r, q2r)
        String[] to_remove = new String[] {"a", "q1", "q2", "q1r", "q2r"};
        for (String _v_remove : to_remove){
            _hsContIVars.remove(_v_remove);
            _hsContAllVars.remove(_v_remove);
        }
        
        // Ensure nonnegativity of dq2 and dq3 by dq2 = max(0, dq2); dq3 = max(0, dq3)
        // argmax = enforceNonnegativity(argmax);

        // // To test solutions...
        // Double[][] testSet = new Double[][] {{0.0, 20.0, 30.0}, {10.0, 90.0, 90.0}, {10.0, 115.0, 95.0},
        //                                      {20.0, 50.0, 70.0}, {100.0, 105.0, 90.0}, {220.0, 50.0, 70.0},
        //                                      {230.0, 117.0, 95.0}, {230.0, 100.0, 100.0}, {230.0, 120.0, 100.0},
        //                                      {5.0, 118.0, 90.0}, {230.0, 125.0, 95.0}};
        // for (int k=0; k<testSet.length; k++){
        //     Double[] test_k = testSet[k];
        //     int res_k = substituteForEvaluation(lp, new String[] {"q1", "q2", "q3"}, test_k);
        //     int res_dq2 = substituteForEvaluation(argmax.get("dq2_nn"), new String[] {"q1", "q2", "q3"}, test_k);
        //     int res_dq3 = substituteForEvaluation(argmax.get("dq3_nn"), new String[] {"q1", "q2", "q3"}, test_k);
        
        //     System.out.println("Test "+k+":\t(q1, q2, q3)="+Arrays.toString(test_k));
        //     System.out.println("\tLP objective: " + _context.getString(res_k));
        //     System.out.println("\tdq2="+_context.getString(res_dq2)+", dq3="+_context.getString(res_dq3)+"\n");
                
            
        // }                                             

        // for (Map.Entry<String, CAction> kv: _hmName2Action.entrySet()) {
        //     modifyActionTransitions(kv.getKey(), kv.getValue(), argmax);
        // }
    }

    private HashMap<String, Integer> enforceNonnegativity(HashMap<String, Integer> argmax){
        HashMap<String, Integer> modArgMax = new HashMap<String, Integer>();
        for (Map.Entry<String, Integer> me : argmax.entrySet()) {
            String v = me.getKey();
            Integer v_id = me.getValue();
            modArgMax.put(v, v_id);

            v_id = _context.apply(v_id, _context.ZERO, _context.MAX, new int[] {});
            v = v + "_nn";
            modArgMax.put(v, v_id);
        }
        return modArgMax;
    }

    private int enforceDomainConstraint(HashMap<Decision, Boolean> domain_constraint, int xadd, double lowest_value){
        double _lowVal = lowest_value;
        int i = 0;
        for (Map.Entry<Decision, Boolean> me : domain_constraint.entrySet()){
            // double high_val = Double.POSITIVE_INFINITY;
            // double low_val = lowest_value; // Double.NEGATIVE_INFINITY;
            // int constraint = _context.getVarNode(me.getKey(), _lowVal - i * 0.001, high_val);
            int constraint = _context.getVarNode(me.getKey(), 0, 1);
            // xadd = _context.apply(constraint, xadd, _context.MIN);
            xadd = _context.apply(constraint, xadd, _context.PROD);
            i++;
        }
        // xadd = _context.reduceLP(_context.reduceLinearize(xadd));
        return xadd;
    }


    private int substituteForEvaluation(int xadd, String[] _vars, double[] _vals){
        HashMap<String, ArithExpr> subs = new HashMap<String, ArithExpr>();
        int i = 0;
        for (String v : _vars){
            subs.put(v, new DoubleExpr(_vals[i]));
            i++;
        }
        xadd = _context.substitute(xadd, subs);
        return xadd;
    }
    
    private void modifyActionTransitions(String action, CAction caction, HashMap<String, Integer> subs) {
        HashMap<String, ArithExpr> actSub = new HashMap<String, ArithExpr>();
        Double actionVal = Double.parseDouble(action.split("a")[1]);
        actSub.put("a", new DoubleExpr(actionVal));
        HashMap<String, Integer> subsWithAction = new HashMap<String, Integer>();

        // substitute action in argmax substitutions
        for (Map.Entry<String, Integer> kv: subs.entrySet()) {
            Integer ret = caction._camdp._context.substitute(kv.getValue(), actSub);
            ret = _context.reduceLP(_context.reduceLinearize(ret));
            subsWithAction.put(kv.getKey(), ret);
        }

        // substitute in transition expressions
        for (Map.Entry<String, Integer> kv : caction._hmVar2DD.entrySet()) {
            Integer node_id = substituteValuesInNode(kv.getValue(), subsWithAction);
            caction._hmVar2DD.put(kv.getKey(), node_id);
        }

        // substitute in reward expression
        Integer reward = substituteValuesInNode(caction._reward, subsWithAction);
        caction._reward = reward;
    }

    private Integer substituteValuesInNode(Integer node_id, HashMap<String, Integer> subs) {
        /**
         * node_id is id for terminal node.
         * vars inside node_id expression are replaced with xadd provided in subs.
         */

        XADDNode node = _context.getNode(node_id);
        HashSet<String> exprVars = new HashSet<String>();
        node.collectVars(exprVars);
        _context._inequalityToEquality = true;

        for (String var: subs.keySet()) {
            if (exprVars.contains(var)) {
                node_id = _context.reduceProcessXADDLeaf(subs.get(var), _context.new DeltaFunctionSubstitution(var, node_id), true);
            }
        }

        _context._inequalityToEquality = false;
        node_id = _context.reduceLP(_context.reduceLinearize(node_id));
        return node_id;
    }

    ////////////////////////////////////////////////////////////////////////////
    // Main value iteration routine
    ////////////////////////////////////////////////////////////////////////////

    /**
     * CAMDP inference methods
     */
    public int solve(int max_iter) {
        //////////////////////////////////////////////////////////////////////////
        // Value iteration statistics
        _nCurIter = 0;
        if (max_iter < 0)
            max_iter = _nMaxIter;
        else
            _nMaxIter = max_iter;

        int totalTime = 0;
        long[] time = new long[max_iter + 1];
        int[] num_nodes = new int[max_iter + 1];
        int[] num_leaves = new int[max_iter + 1];
        int[] num_branches = new int[max_iter + 1];

        //////////////////////////////////////////////////////////////////////////

        // Initialize value function to zero
        _valueDD = _context.ZERO;

        // Perform value iteration for specified number of iterations, or until convergence detected
        while (_nCurIter < max_iter) {
            ++_nCurIter;
            resetTimer();
            _logStream.println(ASCII_BAR + "\nITERATION #" + _nCurIter + ", " +
                    memDisplay() + " bytes, " + getElapsedTime() + " ms\n" + ASCII_BAR);
            _logStream.flush();

            // Prime diagram
            _prevDD = _valueDD;

            // Iterate over each action
            _maxDD = null;
            for (Map.Entry<String, CAction> me : _hmName2Action.entrySet()) {

                // Regress the current value function through each action (finite number of continuous actions)
                resetTimer(0);
                int regr = _qfunHelper.regress(_valueDD, me.getValue());
                if (EFFICIENCY_DEBUG) System.out.println("Regression Time for "+me.getKey()+" in iter "+_nCurIter+" = "+getElapsedTime(0));
                regr = standardizeDD(regr); 
                if (DISPLAY_POSTMAX_Q)
                    doDisplay(regr, "Q-" + me.getKey() + "^" + _nCurIter + makeApproxLabel());

                // Maintain running max over different actions
                resetTimer(0);
                _maxDD = (_maxDD == null) ? regr : _context.apply(_maxDD, regr, XADD.MAX);
                _maxDD = standardizeDD(_maxDD);
                if (EFFICIENCY_DEBUG) System.out.println("Standardize MaxDD Time for "+me.getKey()+" in iter "+_nCurIter+" = "+getElapsedTime(0));

                // Optional post-max approximation
                if (APPROX_ALWAYS){
                    resetTimer(0);
                    _maxDD = approximateDD(_maxDD);
                    _maxDD = standardizeDD(_maxDD);
                    if (EFFICIENCY_DEBUG) System.out.println("Approx Always & Standardize Time for "+me.getKey()+" in iter "+_nCurIter+" = "+getElapsedTime(0));
                }
                
                if (DISPLAY_MAX)
                    doDisplay(_maxDD, "QMax^" + _nCurIter + makeApproxLabel() );
                _logStream.println("Running max in iter " + _nCurIter + ":" + _context.getString(_maxDD));
                flushCaches();
            }
            // _maxDD should already be Canonical/LPpruned, check
            _valueDD = _maxDD;
            checkStandardDD(_valueDD);
            
            resetTimer(0);
            _valueDD = approximateDD(_valueDD);
            if (EFFICIENCY_DEBUG && APPROX_PRUNING) System.out.println("Approximation Finish on iter " + _nCurIter +"  pruning took: " + getElapsedTime(0));

            //////////////////////////////////////////////////////////////////////////
            // Value iteration statistics
            time[_nCurIter] = getElapsedTime();
            totalTime += time[_nCurIter];
            num_nodes[_nCurIter] = _context.getNodeCount(_valueDD);
            num_leaves[_nCurIter] = _context.getLeafCount(_valueDD);
            num_branches[_nCurIter] = _context.getBranchCount(_valueDD);

            System.out.println("Iter:" + _nCurIter + " Complete. Took: "+time[_nCurIter]+"ms, Nodes = "+num_nodes[_nCurIter]+", Memory = "+memDisplay() +" bytes.");
            _logStream.println("Iter complete:" + _nCurIter + _context.getString(_valueDD));
            if (_nCurIter > 5){//== max_iter){
                doDisplay(_valueDD, "V^" + _nCurIter + makeApproxLabel());
            }
            

            if (LINEAR_PROBLEM && APPROX_PRUNING){
                double maxVal = _context.linMaxVal(_valueDD);;
                double maxRelErr = Double.NaN;
                if (COMPARE_OPTIMAL) {
                    if (APPROX_ERROR == 0d) { //Exact solution
                        optimalMaxValueList.add(maxVal);
                        if (optimalDDList.size() != _nCurIter - 1)
                            System.err.println("Incorrect optimalDD:" + optimalDDList + " " + _nCurIter);
                        optimalDDList.add(_valueDD);
                    }
                    if (optimalDDList.size() > _nCurIter - 1) {
                        maxRelErr = (_context.linMaxDiff(optimalDDList.get(_nCurIter - 1), _valueDD)) / optimalMaxValueList.get(_nCurIter);
                    } else maxRelErr = -1;
                }
              //APPROX_TEST LOG, outputs: iter, #node, #branches, #UsedMem(MB), IterTime, TotTime, MaxVal, RelErr
                _testLogStream.format("%d %d %d %d %d %d %d %f %f\n", _nCurIter, num_nodes[_nCurIter],
                        num_leaves[_nCurIter], num_branches[_nCurIter], usedMem(),
                        time[_nCurIter], totalTime,
                        _context.linMaxVal(_valueDD), maxRelErr);
            }
            _logStream.println("Value function size @ end of iteration " + _nCurIter +
                    ": " + num_nodes[_nCurIter] + " nodes = " +
                    num_branches[_nCurIter] + " cases" + " in " + time[_nCurIter] + " ms");
            
            //////////////////////////////////////////////////////////////////////////
            //Verify Early Convergence
            if (_prevDD.equals(_valueDD)) {
                System.out.println("CAMDP: Converged to solution early,  at iteration " + _nCurIter);
                // Store Optimal solution for all horizons for comparison
                if (LINEAR_PROBLEM && APPROX_PRUNING && COMPARE_OPTIMAL){
                    int it = _nCurIter;
                    while (++it < max_iter) {
                        optimalMaxValueList.add(optimalMaxValueList.get(_nCurIter));
                        optimalDDList.add(_valueDD);
                        //APPROX_TEST LOG, outputs: iter, #node, #branches, #UsedMem(MB), IterTime, TotTime, MaxVal, RelErr
                        _testLogStream.format("%d %d %d %d %d %d %d %f %f\n", it, num_nodes[_nCurIter], num_leaves[_nCurIter],
                            num_branches[_nCurIter], usedMem(),
                            time[_nCurIter], totalTime,
                            optimalMaxValueList.get(_nCurIter), 0.0);
                    }
                }
                break;
            }
        }

        flushCaches();

        //////////////////////////////////////////////////////////////////////////
        // Performance Logging
        _logStream.println("\nValue iteration complete!");
        _logStream.println(max_iter + " iterations took " + getElapsedTime() + " ms");
        _logStream.println("Canonical / non-canonical: " + OperExpr.ALREADY_CANONICAL + " / " + OperExpr.NON_CANONICAL);

        _logStream.println("\nIteration Results summary");
        for (int i = 1; i <= max_iter; i++) {
            String branch_count = num_branches[i] >= 0
                    ? "" + num_branches[i] : " > " + XADD.MAX_BRANCH_COUNT;
            _logStream.println("Iter " + i + ": nodes = " + num_nodes[i] + "\tbranches = " + branch_count + "\ttime = " + time[i] + " ms");
        }
        //////////////////////////////////////////////////////////////////////////

        return _nCurIter;
    }

    public static void ExitOnError(String msg) {
        System.err.println(msg);
        System.exit(1);
    }

    ////////// DD Property Tests /////////////////////////
    public int standardizeDD(int dd){
        if (XADD.ROUND_PRECISION!= null) {dd = _context.reduceRound(dd); checkRound(dd);}
        dd = _context.makeCanonical(dd); checkCanon(dd);//Always use Canonization
        if (LINEAR_PROBLEM) {dd = _context.reduceLP(dd); while (!checkReduceLP(dd)) dd = _context.reduceLP(dd);}
        checkStandardDD(dd);
        return dd;
    }
    public boolean checkStandardDD(int dd){
        boolean standard = true;
        if (XADD.ROUND_PRECISION!= null && !checkRound(dd)) standard = false;
        if (!checkCanon(dd)) standard = false;//Always use Canonization
        if (LINEAR_PROBLEM && !checkReduceLP(dd)) standard = false;
        return standard;
    }
    private boolean checkRound(int dd) {
        int roundDD = _context.reduceRound(dd);
        if (roundDD != dd){
            System.err.println("Check Round fail");
            if (!SILENCE_ERRORS_PLOTS){
                _context.getGraph(dd).launchViewer("ERROR diagram 1: original DD");
                _context.getGraph(roundDD).launchViewer("ERROR diagram 2: reduceRound(DD)");
            }
            return false;
        }
        return true;
    }
    private boolean checkCanon(int dd) {
        //Error checking and logging
        int canonDD = _context.makeCanonical(dd);
        if (dd != canonDD) {
            System.err.println("Check Canon fail: OriDD: "+dd+" size = "+_context.getNodeCount(dd)+", Canon DD Size="+_context.getNodeCount(canonDD));
            displayDifError(dd, canonDD);
            dd = _context.makeCanonical(dd); //repeat command for Debugging
            canonDD = _context.makeCanonical(dd);
            return false;
        }
        return true;
    }
    public void displayDifError(int dd, int newDD) {
        if (!SILENCE_ERRORS_PLOTS){
            doDisplay(dd,"ERROR plot 1: original");
            doDisplay(newDD,"ERROR plot 2:resulting");
            int dif = _context.apply(dd, newDD, XADD.MINUS);
            doDisplay(dif,"ERROR plot 3: difference");
        }
    }
    private boolean checkReduceLP(int dd) {
        //Error checking and logging
        int reduLPDD = _context.reduceLP(dd);
        if (dd != reduLPDD) {
            System.err.println("Check ReduceLP fail: OriDD: "+dd+" size = "+_context.getNodeCount(dd)+", Pruned DD Size="+_context.getNodeCount(reduLPDD));
            displayDifError(dd, reduLPDD);
            dd = _context.reduceLP(dd); //repeat command for Debugging
            reduLPDD = _context.reduceLP(dd);
            return false;
        }
        return true;
    }
    public int approximateDD(int dd){
        if (LINEAR_PROBLEM && APPROX_PRUNING && APPROX_ERROR > 0)
            dd = _context.linPruneRel(dd, APPROX_ERROR);
        return dd;
    }
    
    ////////////////////////////////////////////////////////////////////////////
    // Miscellaneous
    ////////////////////////////////////////////////////////////////////////////

    public Double evaluateInitialS(int valueDD){
        if (_initialS == null){
            System.err.println("Trying to Evaluate initial State on a CAMDP without it.");
            return Double.NaN;
        }
        return evaluateState(valueDD, _initialS);
    }
    public Double evaluateState(int valueDD, State s){
        return _context.evaluate(valueDD, s._hmBoolVars, s._hmContVars);
    }    
    public void flushCaches() {
        flushCaches(new ArrayList<Integer>());
    }

    public void flushCaches(boolean forceFlush) {
        flushCaches(new ArrayList<Integer>(), forceFlush);
    }

    public void flushCaches(List<Integer> special_nodes) {
        flushCaches(special_nodes, false);
    }

    public void flushCaches(List<Integer> special_nodes, boolean forceFlush) {

        if (((double) RUNTIME.freeMemory() /
                (double) RUNTIME.totalMemory()) > FLUSH_PERCENT_MINIMUM && !forceFlush) {
            //System.out.println("No need to flush caches.");
            return; // Still enough free mem to exceed minimum requirements
        }

        // Commence cache flushing
        _logStream.println("Before flush: " + _context._hmInt2Node.size() + " XADD nodes in use, " + "freeMemory: " +
                _df.format(RUNTIME.freeMemory() / 10e6d) + " MB = " +
                _df.format(100d * RUNTIME.freeMemory() / (double) RUNTIME.totalMemory()) + "% available memory");

        // TODO: Maybe keeping these is worthwhile?
        _hmContRegrCache.clear();

        _context.clearSpecialNodes();
        for (Integer node : special_nodes)
            _context.addSpecialNode(node);


        for (CAction a : _hmName2Action.values()) {
            _context.addSpecialNode(a._reward);
            for (Integer xadd : a._hmVar2DD.values())
                _context.addSpecialNode(xadd);
            for (Integer xadd : a._hmNoise2DD.values())
                _context.addSpecialNode(xadd);
        }
        if (_prevDD != null && !forceFlush) {
            _context.addSpecialNode(_prevDD);
        }
        if (_maxDD != null && !forceFlush) {
            _context.addSpecialNode(_maxDD);
        }
        if (_valueDD != null && !forceFlush) {
            _context.addSpecialNode(_valueDD);
        }
        if (optimalDDList != null && optimalDDList.size()>1) //keep even at forceFlush, because we want to measure the error
            _context._hsSpecialNodes.addAll(optimalDDList.subList(1, optimalDDList.size()-1));
        _context.flushCaches();

        _logStream.println("After flush: " + _context._hmInt2Node.size() + " XADD nodes in use, " + "freeMemory: " +
                _df.format(RUNTIME.freeMemory() / 10e6d) + " MB = " +
                _df.format(100d * RUNTIME.freeMemory() / (double) RUNTIME.totalMemory()) + "% available memory");
    }


    public String toString() {
        return toString(true, false);
    }

    public String toString(boolean display_reward, boolean display_value) {
        StringBuffer sb = new StringBuffer();
        sb.append("\nCMDP Definition:\n===============\n");
        sb.append("BVars:       " + _hsBoolAllVars + " = S:" + _hsBoolSVars + " + I:" + _hsBoolIVars + " = XADD (all vars): " + _context._alBooleanVars + "\n");
        sb.append("NS BVars:    " + _hsBoolNSVars + "\n");
        sb.append("CVars:       " + _hsContAllVars + " = S:" + _hsContSVars + " + A:" + _hsContAVars + " + I:" + _hsContIVars + "\n");
        sb.append("NS CVars:    " + _hsContNSVars + "\n");
        sb.append("Noise vars:  " + _hsNoiseVars + "\n");
        sb.append("Min-values:  " + _context._hmMinVal + "\n");
        sb.append("Max-values:  " + _context._hmMaxVal + "\n");
        sb.append("Order:       " + _context._alOrder + "\n");
        sb.append("Iterations:  " + _nMaxIter + "\n");
        sb.append("Linearity:  " + LINEAR_PROBLEM + "\n");
        //sb.append("Constraints (" + _alConstraints.size() + "):\n");
        //for (Integer cons : _alConstraints) {
        //    sb.append("- " + _context.getString(cons) + "\n");
        //}
        if (_initialS != null) {
            sb.append("Initial State: " + _initialS + "\n");    
        }
        sb.append("Actions (" + _hmName2Action.size() + "):\n");
        for (CAction a : _hmName2Action.values()) {
            sb.append("\n==> " + a);
        }
        sb.append("\n");

        if (display_value) {
            Graph g = _context.getGraph(_valueDD);
            g.launchViewer(1300, 770);
        }

        return sb.toString();
    }

    public String makeApproxLabel(){
        return APPROX_PRUNING?"":"-" + String.format("%03d", Math.round(1000 * APPROX_ERROR));
    }
    public void doDisplay(int xadd_id, String label) {
        exportXADD(xadd_id, label); // Exports DAG, can read in later and view using XADDViewer
        // Boolean toPlot = (_nCurIter == _nMaxIter);
        // Boolean toPlot = true;
        Boolean toPlot = ((_nCurIter % 1) == 0 || (_nCurIter == 1) || (_nCurIter == _nMaxIter));
        if (DISPLAY_V && toPlot)
            displayGraph(xadd_id, label);
        if (DISPLAY_2D && toPlot)
            display2D(xadd_id, label);
        if (DISPLAY_3D && toPlot)
            display3D(xadd_id, label);
    }

    public void exportXADD(int xadd_id, String label) {
        label = label.replace(".csamdp", "").replace(".camdp", "").replace(".cmdp", "")
                .replace('^', '_').replace("(", "").replace(")", "").replace(":", "_").replace(" ", "");
        String xadd_filename = _logFileRoot + "." + label + ".xadd";
        _context.exportXADDToFile(xadd_id, xadd_filename);

        // Copy over plotting options if they exist
        File file2D = new File(_problemFile + ".2d");
        if (file2D.exists()) {
            FileOptions opt = new FileOptions(_problemFile + ".2d");
            opt.exportToFile(xadd_filename + ".2d");
        }
        File file3D = new File(_problemFile + ".3d");
        if (file3D.exists()) {
            FileOptions opt = new FileOptions(_problemFile + ".3d");
            opt.exportToFile(xadd_filename + ".3d");
        }
    }

    public void displayGraph(int xadd_id, String label) {
        String[] split = label.split("[\\\\/]");
        label = split[split.length - 1];
        label = label.replace(".csamdp", "").replace(".camdp", "").replace(".cmdp", "");
    
        Graph g;
        int count;
        if (DONT_SHOW_HUGE_GRAPHS && (count = _context.getNodeCount(xadd_id)) > MAXIMUM_XADD_DISPLAY_SIZE){
            g = new Graph();
            g.addNode("_count_");
            g.addNodeLabel("_count_", "Too Large to Print: "+count+" Nodes");
            g.addNodeShape("_count_", "square");
            g.addNodeStyle("_count_", "filled");
            g.addNodeColor("_count_", "red1");
        }
        else{
            g = _context.getGraph(xadd_id);
        }
        g.addNode("_temp_");
        g.addNodeLabel("_temp_", label);
        g.addNodeShape("_temp_", "square");
        g.addNodeStyle("_temp_", "filled");
        g.addNodeColor("_temp_", "gold1");
        String safe_filename = label.replace('^', '_').replace("(", "").replace(")", "").replace(":", "_").replace(" ", "");
        g.genDotFile(_logFileRoot + "." + safe_filename + ".dot");

        g.launchViewer(label);
    }

    public void display2D(int xadd_id, String label) {

        // If DISPLAY_2D is enabled, it is expected that necessary parameters
        // have been placed in a _problemFile + ".2d"
        FileOptions opt = new FileOptions(_problemFile + ".2d");

        if (!SILENT_PLOT) {
            System.out.println("Plotting 2D...");
            System.out.println("var: " + opt._var.get(0) + ", [" + opt._varLB.get(0) + ", " +
                    opt._varInc.get(0) + ", " + opt._varUB.get(0) + "]");
            System.out.println("bassign: " + opt._bassign);
            System.out.println("dassign: " + opt._dassign);
        }

        XADDUtils.PlotXADD(_context, xadd_id,
                opt._varLB.get(0), opt._varInc.get(0), opt._varUB.get(0),
                opt._bassign, opt._dassign, opt._var.get(0), _logFileRoot + "." + label);
    }

    public void display3D(int xadd_id, String label) {

        // If DISPLAY_3D is enabled, it is expected that necessary parameters
        // have been placed in a _problemFile + ".3d"
        FileOptions opt = new FileOptions(_problemFile + ".3d");

        if (!SILENT_PLOT) {
            System.out.println("Plotting 3D...");
            System.out.println("var: " + opt._var.get(1) + ", [" + opt._varLB.get(1) + ", " +
                    opt._varInc.get(1) + ", " + opt._varUB.get(1) + "]");
            System.out.println("bassign: " + opt._bassign);
            System.out.println("dassign: " + opt._dassign);
        }

        XADDUtils.Plot3DSurfXADD(_context, xadd_id,
                opt._varLB.get(0), opt._varInc.get(0), opt._varUB.get(0),
                opt._varLB.get(1), opt._varInc.get(1), opt._varUB.get(1),
                opt._bassign, opt._dassign, opt._var.get(0), opt._var.get(1), _logFileRoot + "." + label);
    }

    public void display3D(int xadd_id, String label, String file_name) {

        // If DISPLAY_3D is enabled, it is expected that necessary parameters
        // have been placed in a file_name + ".3d"
        FileOptions opt = new FileOptions(file_name + ".3d");

        if (!SILENT_PLOT) {
            System.out.println("Plotting 3D...");
            System.out.println("var: " + opt._var.get(1) + ", [" + opt._varLB.get(1) + ", " +
                    opt._varInc.get(1) + ", " + opt._varUB.get(1) + "]");
            System.out.println("bassign: " + opt._bassign);
            System.out.println("dassign: " + opt._dassign);
        }

        XADDUtils.Plot3DSurfXADD(_context, xadd_id,
                opt._varLB.get(0), opt._varInc.get(0), opt._varUB.get(0),
                opt._varLB.get(1), opt._varInc.get(1), opt._varUB.get(1),
                opt._bassign, opt._dassign, opt._var.get(0), opt._var.get(1), _logFileRoot + "." + label);
    }

    // A helper class to load options for 2D and 3D plotting for specific problems
    public static class FileOptions {
        public ArrayList<String> _var = new ArrayList<String>();
        public ArrayList<Double> _varLB = new ArrayList<Double>();
        public ArrayList<Double> _varInc = new ArrayList<Double>();
        public ArrayList<Double> _varUB = new ArrayList<Double>();
        public HashMap<String, Boolean> _bassign = new HashMap<String, Boolean>();
        public HashMap<String, Double> _dassign = new HashMap<String, Double>();

        public FileOptions() {
        }

        public FileOptions(String filename) {
            String line = null;
            try {
                BufferedReader br = new BufferedReader(new FileReader(filename));
                while ((line = br.readLine()) != null) {
                    line = line.trim();
                    if (line.length() == 0)
                        continue;
                    String[] split = line.split("\\s+"); // Luis: need general whitespace regex since previous files use \t
                    String label = split[0].trim();
                    //System.out.println("Label: '" + label + "'");
                    if (label.equalsIgnoreCase("var")) {
                        // Line format: var name lb inc ub
                        _var.add(split[1].trim());
                        _varLB.add(Double.parseDouble(split[2]));
                        _varInc.add(Double.parseDouble(split[3]));
                        _varUB.add(Double.parseDouble(split[4]));
                    } else if (label.equalsIgnoreCase("bassign")) {
                        // Line format: bassign name {true,false}
                        _bassign.put(split[1].trim(), Boolean.parseBoolean(split[2]));
                    } else if (label.equalsIgnoreCase("cassign")) {
                        // Line format: cassign name double
                        _dassign.put(split[1].trim(), Double.parseDouble(split[2]));
                    } else {
                        throw new Exception("ERROR: Unexpected line label '" + label + "', not {var, bassign, cassign}");
                    }
                }
            } catch (Exception e) {
                System.err.println(e + "\nContent at current line: '" + line + "'");
                System.err.println("ERROR: could not read file: " + filename + ", exiting.");
            }
        }

        public void exportToFile(String outfile) {
            try {
                PrintStream ps = new PrintStream(new FileOutputStream(outfile));
                for (int i = 0; i < _var.size(); i++) {
                    String var = _var.get(i);
                    double lb = _varLB.get(i);
                    double inc = _varInc.get(i);
                    double ub = _varUB.get(i);
                    ps.println("var\t" + var + "\t" + lb + "\t" + inc + "\t" + ub);
                }
                for (Map.Entry<String, Boolean> me : _bassign.entrySet())
                    ps.println("bassign\t" + me.getKey() + "\t" + me.getValue());
                for (Map.Entry<String, Double> me : _dassign.entrySet())
                    ps.println("dassign\t" + me.getKey() + "\t" + me.getValue());
                ps.close();
            } catch (Exception e) {
                System.err.println("WARNING: could not export " + outfile);
            }
        }
    }

    // Reset elapsed time
    public static void resetTimer() {
        _lTime = System.currentTimeMillis();
    }

    // Get the elapsed time since resetting the timer
    public static long getElapsedTime() {
        return System.currentTimeMillis() - _lTime;
    }

    // Reset elapsed time
    public static void resetTimer(int n) {
        _lTimers[n] = System.currentTimeMillis();
    }

    // Get the elapsed time since resetting the timer
    public static long getElapsedTime(int n) {
        return System.currentTimeMillis() - _lTimers[n];
    }
    
    
    public static String memDisplay() {
        long total = RUNTIME.totalMemory();
        long free = RUNTIME.freeMemory();
        return total - free + ":" + total;
    }

    public static int usedMem() {
        long total = RUNTIME.totalMemory();
        long free = RUNTIME.freeMemory();
        return (int) ((total - free) / 1000000);
    }

    ////////////////////////////////////////////////////////////////////////////
    // Testing Interface
    ////////////////////////////////////////////////////////////////////////////

    public static String insertDirectory(String filename, String add_dir) {
        try {
            File f = new File(filename);
            String parent = f.getParent();
            String dir_path = (parent == null ? "" : parent) + File.separator + add_dir;
            File dir = new File(dir_path);
            if (dir.exists() && !dir.isDirectory())
                throw new Exception("'" + dir + "' is a file, cannot change it to a directory for logging.");
            if (!dir.exists())
                dir.mkdir();
            return dir_path + File.separator + f.getName();
        } catch (Exception e) {
            System.err.println("Could not insert directory '" + add_dir + "' into '" + filename + "' to produce output files.");
            System.exit(1);
        }
        return null;
    }

    public ArrayList<String> intern(ArrayList<String> l) {
        ArrayList<String> ret = new ArrayList<String>();
        for (String s : l)
            ret.add(s.intern());
        return ret;
    }

    public static void usage() {
        System.out.println("\nUsage: MDP-filename #iter display-2D? display-3D? [dApproxPrune]");
        System.exit(1);
    }

    public void setApproxTest(double eps, PrintStream log, boolean always) {
        APPROX_ERROR = eps;
        _testLogStream = log;
        APPROX_ALWAYS = always;
        COMPARE_OPTIMAL = true;
    }

    public static void main(String args[]) {
        if (args.length < 4 || args.length > 5) {
            usage();
        }

        // Parse problem filename
        String filename = args[0];

        // Parse iterations
        int iter = -1;
        try {
            iter = Integer.parseInt(args[1]);
        } catch (NumberFormatException nfe) {
            System.out.println("\nIllegal iteration value\n");
            usage();
        }

        // Build a CAMDP, display, solve
        CAMDP mdp = new CAMDP(filename);
        mdp.DISPLAY_2D = Boolean.parseBoolean(args[2]);
        mdp.DISPLAY_3D = Boolean.parseBoolean(args[3]);

        //aditional argument modifies
        if (args.length == 5) {
            mdp.APPROX_ERROR = Double.parseDouble(args[4]);
        }
        //System.out.println(mdp.toString(false, false));
        System.out.println(mdp.toString(false, false));
        //System.in.read();

        int iter_used = mdp.solve(iter);
//        System.out.println("\nSolution complete, required " + 
//                iter_used + " / " + iter + " iterations.");
        //mdp._context.showCacheSize();
//        mdp.flushCaches(true);
//        mdp._context.showCacheSize();
        System.out.println("CAMDP-FINISH");
    }

    public final static String ASCII_BAR = "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"; // Display shortcut
}
