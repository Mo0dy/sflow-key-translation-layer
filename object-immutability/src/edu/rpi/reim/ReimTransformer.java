package edu.rpi.reim;

import java.util.*;
import java.lang.annotation.*;
import java.util.regex.Pattern;

import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.PackManager;
import soot.PatchingChain;
import soot.RefLikeType;
import soot.RefType;
import soot.Type;
import soot.VoidType;
import soot.PrimType;
import soot.NullType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.SootField;
import soot.MethodSource;
import soot.Transform;
import soot.Unit;
import soot.Value;
import soot.jimple.*;
import soot.options.Options;
import soot.tagkit.*; 
import edu.rpi.Constraint.SubtypeConstraint;
import edu.rpi.Constraint.EqualityConstraint;
import edu.rpi.AnnotatedValue.FieldAdaptValue;
import edu.rpi.AnnotatedValue.MethodAdaptValue;
import edu.rpi.AnnotatedValue.Kind;
import edu.rpi.*;
import edu.rpi.ConstraintSolver.FailureStatus;
import checkers.inference.sflow.quals.*;
import checkers.inference.reim.quals.*;


public class ReimTransformer extends InferenceTransformer {


    private Set<Annotation> sourceAnnos;

    public final Annotation READONLY;

    public final Annotation POLYREAD;

    public final Annotation MUTABLE;

	/** For default pure method */
	private List<Pattern> defaultPurePatterns = null;

    private Set<String> defaultReadonlyRefTypes = null;
        
    private HashMap<SootMethod,HashSet<AnnotatedValue>> parameters = new HashMap<SootMethod,HashSet<AnnotatedValue>>();

    public ReimTransformer() {

        READONLY = AnnotationUtils.fromClass(Readonly.class);
        POLYREAD = AnnotationUtils.fromClass(Polyread.class);
        MUTABLE = AnnotationUtils.fromClass(Mutable.class);

        sourceAnnos = AnnotationUtils.createAnnotationSet();
        sourceAnnos.add(READONLY);
        sourceAnnos.add(POLYREAD);
        sourceAnnos.add(MUTABLE);

		defaultPurePatterns = new ArrayList<Pattern>(5);
        defaultPurePatterns.add(Pattern.compile("[^ \t]* equals\\(java\\.lang\\.Object\\)$"));
        defaultPurePatterns.add(Pattern.compile("[^ \t]* hashCode\\(\\)$"));
        defaultPurePatterns.add(Pattern.compile("[^ \t]* toString\\(\\)$"));
        defaultPurePatterns.add(Pattern.compile("[^ \t]* compareTo\\(.*\\)$"));

        defaultReadonlyRefTypes = new HashSet<String>();
        defaultReadonlyRefTypes.add("java.lang.String");
        defaultReadonlyRefTypes.add("java.lang.Boolean");
        defaultReadonlyRefTypes.add("java.lang.Byte");
        defaultReadonlyRefTypes.add("java.lang.Character");
        defaultReadonlyRefTypes.add("java.lang.Double");
        defaultReadonlyRefTypes.add("java.lang.Float");
        defaultReadonlyRefTypes.add("java.lang.Integer");
        defaultReadonlyRefTypes.add("java.lang.Long");
        defaultReadonlyRefTypes.add("java.lang.Number");
        defaultReadonlyRefTypes.add("java.lang.Short");
        defaultReadonlyRefTypes.add("java.util.concurrent.atomic.AtomicInteger");
        defaultReadonlyRefTypes.add("java.util.concurrent.atomic.AtomicLong");
        defaultReadonlyRefTypes.add("java.math.BigDecimal");
        defaultReadonlyRefTypes.add("java.math.BigInteger");
    }


	public boolean isDefaultReadonlyType(Type t) {
        if (t instanceof PrimType)
            return true;
        if (defaultReadonlyRefTypes.contains(t.toString()))
            return true;
        return false;
    }

	/**
	 * Check if the method is default pure. E.g. We assume 
	 * java.lang.Object.toString() is default pure. 
	 * @param methodElt
	 * @return
	 */
	public boolean isDefaultPureMethod(SootMethod sm) {
		String key = sm.getSubSignature();
		for (Pattern p : defaultPurePatterns) {
			if (p.matcher(key).matches()) {
				return true;
			}
		}
		return false;
	}

    @Override
    protected boolean isAnnotated(AnnotatedValue v) {
        Set<Annotation> diff = v.getRawAnnotations();
        diff.retainAll(sourceAnnos);
        return !diff.isEmpty();
    }

    @Override
    protected AnnotatedValue createFieldAdaptValue(AnnotatedValue context, 
            AnnotatedValue decl, AnnotatedValue assignTo) {
        return new FieldAdaptValue(context, decl);
    }

    @Override
    protected AnnotatedValue createMethodAdaptValue(AnnotatedValue receiver, 
            AnnotatedValue decl, AnnotatedValue assignTo) {
        if (assignTo == null)
            return decl;
        else 
            return new MethodAdaptValue(assignTo, decl);
    }

    @Override
    protected InferenceVisitor getInferenceVisitor(InferenceTransformer t) {
        return new InferenceVisitor(t);
    }

	@Override
	public Set<Annotation> getSourceLevelQualifiers() {
		return sourceAnnos;
	}

    @Override
    protected void annotateArrayComponent(AnnotatedValue v, Object o) {
        if (!isAnnotated(v)) {
            v.addAnnotation(READONLY);
            v.addAnnotation(POLYREAD);
        }
    }

    @Override
    protected void annotateField(AnnotatedValue v, SootField field) {
        if (!isAnnotated(v)) {
            /*if (field.getName().equals("this$0")) {
                v.setAnnotations(sourceAnnos, this);
            } else*/ if (isDefaultReadonlyType(v.getType())) {
                v.addAnnotation(READONLY);
            } else if (!field.isStatic()) {
                v.addAnnotation(READONLY);
                v.addAnnotation(POLYREAD);
            } else
                v.setAnnotations(sourceAnnos, this);
        }
    }

    @Override
    protected void annotateThis(AnnotatedValue v, SootMethod method) {
        if (!isAnnotated(v) && !method.isStatic()) {
            if (isDefaultReadonlyType(v.getType()) && !method.isConstructor()) {
                v.addAnnotation(READONLY);
            } else if (isLibraryMethod(method)) {
            	// System.out.println("Annotating a library method with default MUTABLE: "+method);
                v.addAnnotation(MUTABLE);
            	// v.addAnnotation(READONLY); // ANA, will change!
            } else
                v.setAnnotations(sourceAnnos, this);
            
        }
        // ANA: added to check if any lib is annotated.
        else {
        	System.out.println("Annotated lib: "+method+" is annotated: "+isAnnotated(v) + v.getAnnotations(this).toString());
        }
    }

    @Override
    protected void annotateParameter(AnnotatedValue v, SootMethod method, int index) {
        if (!isAnnotated(v)) {
            if (isDefaultReadonlyType(v.getType())) {
                v.addAnnotation(READONLY);
            } else if (isLibraryMethod(method)) {
                v.addAnnotation(MUTABLE);
            } else 
                v.setAnnotations(sourceAnnos, this);
        }
        // ANA Collecting method parameters. To determine which methods have only READONLY parameters
        HashSet<AnnotatedValue> parameterSet = parameters.get(method);
        if (parameterSet == null) {
        	parameterSet = new HashSet<AnnotatedValue>();
        	parameters.put(method,parameterSet);
        }
        parameterSet.add(v);
    }

    @Override
    protected void annotateReturn(AnnotatedValue v, SootMethod method) {
        if (!isAnnotated(v) && method.getReturnType() != VoidType.v()) {
            if (isDefaultReadonlyType(v.getType())) {
                v.addAnnotation(READONLY);
            } else if (isLibraryMethod(method)) {
                v.addAnnotation(READONLY);
                v.addAnnotation(POLYREAD);
            } else 
                v.setAnnotations(sourceAnnos, this);
        }
    }

    @Override
    protected void annotateDefault(AnnotatedValue v, Kind kind, Object o) {
        if (!isAnnotated(v)) {
            if (v.getType() == NullType.v()) 
                v.addAnnotation(MUTABLE);
            else if (kind == Kind.LITERAL)
                v.addAnnotation(READONLY);
            else if (isDefaultReadonlyType(v.getType())) {
                v.addAnnotation(READONLY);
            } else 
                v.setAnnotations(sourceAnnos, this);
        }
    }

    @Override
    protected void handleInstanceFieldWrite(AnnotatedValue aBase, 
            AnnotatedValue aField, AnnotatedValue aRhs) {
        Set<Annotation> set = AnnotationUtils.createAnnotationSet();
        // ANA: change to ignore setting to MUTABLE if simple type field write
        // ANA: TODO: refactor test into a predicate method: isSimpleType(a.getType())
        if (!(aRhs.getType() instanceof RefLikeType)) {
        	super.handleInstanceFieldWrite(aBase, aField, aRhs);
        	//System.out.println("WRITE NOT MUTABLE: "+aField);
        	return;
        }
        // ANA: end of change.
        
        set.add(MUTABLE);
        AnnotatedValue mutableConstant = getAnnotatedValue(
                MUTABLE.annotationType().getCanonicalName(), 
                VoidType.v(), Kind.CONSTANT, null, set);
        addEqualityConstraint(aBase, mutableConstant);        
        
        super.handleInstanceFieldWrite(aBase, aField, aRhs);
    }

    @Override
    protected void handleMethodOverride(SootMethod overrider, SootMethod overridden) {
		// add constraints except that overridden is default pure
        if (!isDefaultPureMethod(overridden))
            super.handleMethodOverride(overrider, overridden);
    }

    @Override
    public int getAnnotationWeight(Annotation anno) {
        return 0;
    }

    @Override
    public FailureStatus getFailureStatus(Constraint c) {
        AnnotatedValue left = c.getLeft();
        AnnotatedValue right = c.getRight();
        if (isDefaultReadonlyType(left.getType()) || left.getKind() == Kind.LITERAL
                || isDefaultReadonlyType(right.getType()) || right.getKind() == Kind.LITERAL)
            return FailureStatus.IGNORE;

        if (isFromLibrary(left) || isFromLibrary(right))
            return FailureStatus.WARN;

        return FailureStatus.ERROR;
    }

    @Override
    public ViewpointAdapter getViewpointAdapter() {
        return new ReimViewpointAdapter();
    }

    @Override
    public boolean isStrictSubtyping() {
        return false;
    }

    @Override
    public String getName() {
        return "reim";
    }
    
    // ANA: returns the readonly inits.
    public HashMap<SootMethod,HashSet<AnnotatedValue>> getParameters() {
    	return parameters;
    }
    /*
    @Override
    protected void addSubtypeConstraint(AnnotatedValue sub, AnnotatedValue sup) {
        if (sub.getKind() == Kind.LITERAL || sup.getKind() == Kind.LITERAL)
            return;
        
        //ANA: Start of ugly code. Will remove.
        // reverses constraint. If x <: q |> this_init, add q |> this_init <: x instead
        if (sup.getKind() == AnnotatedValue.Kind.METH_ADAPT && 
        	((AnnotatedValue.AdaptValue) sup).getDeclValue().getKind() == AnnotatedValue.Kind.THIS && 
        	((AnnotatedValue.AdaptValue) sup).getDeclValue().getEnclosingMethod().getName().equals("<init>")) {
        				// System.out.println("HERE1: "+sup+" <: "+sub);
        				super.addSubtypeConstraint(sup,sub);
        				return;
        }
        // reverses THIS_<init> <: r0_<init> into r0_<init> <: THIS_<init>
        if ((sub.getKind() == AnnotatedValue.Kind.THIS) && 
        	sub.getEnclosingMethod().getName().equals("<init>") && (sup.getKind() == AnnotatedValue.Kind.LOCAL)) {
        		// System.out.println("HERE1!!!: "+sub+" <: "+sup);
        		super.addSubtypeConstraint(sup,sub);
        		return;
        	}
        //ANA: End of ugly code.
         
         
        super.addSubtypeConstraint(sub,sup);
        
        //Constraint c = new SubtypeConstraint(sub, sup);
        //if (!constraints.add(c))
        //    return;
        //addComponentConstraints(sub, sup);
	}
	*/
}
