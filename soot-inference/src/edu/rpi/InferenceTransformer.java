package edu.rpi;

import java.util.Iterator;
import java.util.*;
import java.lang.annotation.*;
import java.io.PrintStream;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import soot.*;
import soot.jimple.AbstractStmtSwitch;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.*;
import soot.jimple.Jimple;
import soot.jimple.StringConstant;
import soot.options.Options;
import soot.tagkit.*; 

import edu.rpi.Constraint.SubtypeConstraint;
import edu.rpi.Constraint.EqualityConstraint;
import edu.rpi.Constraint.UnequalityConstraint;
import edu.rpi.AnnotatedValue.FieldAdaptValue;
import edu.rpi.AnnotatedValue.MethodAdaptValue;
import edu.rpi.AnnotatedValue.AdaptValue;
import edu.rpi.AnnotatedValue.Kind;
import edu.rpi.ConstraintSolver.FailureStatus;
import soot.util.Chain;

import javax.swing.text.html.HTMLDocument;

public abstract class InferenceTransformer extends BodyTransformer {

    private VisitorState visitorState = new VisitorState();

    private Set<Constraint> constraints = new LinkedHashSet<Constraint>();

    private Comparator<SootClass> comparator = new Comparator<SootClass>() {
        public int compare(SootClass o1, SootClass o2) {
            return o1.toString().compareTo(o2.toString());
        }
    };

    private Set<SootClass> visitedClasses = new TreeSet<SootClass>(comparator);

    private boolean needLocals = false;

    private static Map<SootMethod, Map<String, AnnotatedValue>> locals = new HashMap<SootMethod, Map<String, AnnotatedValue>>();

    private static Map<String, AnnotatedValue> adaptValues = new HashMap<String, AnnotatedValue>();

    /**
     * This is actually static, because AnnotatedValueMap.v() always
     * return the same object.
     */
    private AnnotatedValueMap annotatedValues = AnnotatedValueMap.v();

    private ViewpointAdapter vpa = getViewpointAdapter();

    public final static String CALLSITE_PREFIX = "callsite-";

    public final static String FAKE_PREFIX = "fake-";

    public final static String LIB_PREFIX = "lib-";

    public VisitorState getVisitorState() {
        return visitorState;
    }

    protected abstract AnnotatedValue createFieldAdaptValue(AnnotatedValue context, 
            AnnotatedValue decl, AnnotatedValue assignTo);

    protected abstract AnnotatedValue createMethodAdaptValue(AnnotatedValue receiver, 
            AnnotatedValue decl, AnnotatedValue assignTo);

    protected abstract InferenceVisitor getInferenceVisitor(InferenceTransformer t);

    protected abstract boolean isAnnotated(AnnotatedValue v);
    
    public abstract ViewpointAdapter getViewpointAdapter();

	public abstract Set<Annotation> getSourceLevelQualifiers();

    public abstract int getAnnotationWeight(Annotation anno);

    public abstract boolean isStrictSubtyping();

    public abstract FailureStatus getFailureStatus(Constraint c);

    public abstract String getName();

    // Lindsey, Threadfix variables
    private HashMap<Integer, SootMethod> threadFixTable = null;

    private String THREAD_CLASS = "java.lang.Thread";

    private String RUNNABLE_CLASS = "java.lang.Runnable";

    private String OBJ_CLASS = "java.lang.Object";

    private String START_METHOD = "start";

    // private Pattern CONSTRUCTOR_METHOD = Pattern.compile("<init>", Pattern.CASE_INSENSITIVE);

    //private String CONSTRUCTOR_METHOD_UPPER = "<INIT>";
    //private String CONSTRUCTOR_METHOD_LOWER = "<init>";

    private String RUN_METHOD = "run";

    // end threadfix

    protected AnnotatedValue getFieldAdaptValue(AnnotatedValue context, 
            AnnotatedValue decl, AnnotatedValue assignTo) {
        AnnotatedValue av = createFieldAdaptValue(context, decl, assignTo);
        String identifier = av.getIdentifier();
        AnnotatedValue ret = adaptValues.get(identifier);
        if (ret == null) {
            ret = av;
            ret.setEnclosingClass(visitorState.getSootClass());
            ret.setEnclosingMethod(visitorState.getSootMethod());
            adaptValues.put(identifier, ret);
        }
        return ret;
    }

    protected AnnotatedValue getMethodAdaptValue(AnnotatedValue receiver, 
            AnnotatedValue decl, AnnotatedValue assignTo) {
        AnnotatedValue av = createMethodAdaptValue(receiver, decl, assignTo);
        String identifier = av.getIdentifier();
        AnnotatedValue ret = adaptValues.get(identifier);
        if (ret == null) {
            ret = av;
            ret.setEnclosingClass(visitorState.getSootClass());
            ret.setEnclosingMethod(visitorState.getSootMethod());
            adaptValues.put(identifier, ret);
        }
        return ret;
    }

    protected AnnotatedValue getAnnotatedValue(String identifier, Type type, 
            Kind kind, Object v, Set<Annotation> annos) {
        AnnotatedValue ret;
        if (kind == Kind.LOCAL) {
            SootMethod sm = visitorState.getSootMethod();
            Map<String, AnnotatedValue> localMap = locals.get(sm);
            if (localMap == null) {
                localMap = new LinkedHashMap<String, AnnotatedValue>();
                locals.put(sm, localMap);
            }
            ret = localMap.get(identifier);
            if (ret == null) {
                ret = new AnnotatedValue(identifier, type, kind, v, annos);
                ret.setEnclosingClass(visitorState.getSootClass());
                ret.setEnclosingMethod(visitorState.getSootMethod());
                if (v != null)
                    localMap.put(identifier, ret);
            }
        } else {
            ret = annotatedValues.get(identifier);
            if (ret == null) {
                ret = new AnnotatedValue(identifier, type, kind, v, annos);
                ret.setEnclosingClass(visitorState.getSootClass());
                ret.setEnclosingMethod(visitorState.getSootMethod());
                if (kind != Kind.LITERAL)
                    annotatedValues.put(identifier, ret);
            }
        }
        if (!isAnnotated(ret)) {
            if (kind == Kind.COMPONENT) 
                annotateArrayComponent(ret, v);
            else
                annotateDefault(ret, kind, v);
        }
        return ret;
    }

    protected AnnotatedValue getAnnotatedValue(String identifier, Type type, Kind kind, Object v) {
        return getAnnotatedValue(identifier, type, kind, v, AnnotationUtils.createAnnotationSet());
    }

    protected AnnotatedValue getAnnotatedClass(SootClass sc) {
        String identifier = sc.getName() + "@CLASS";
        return getAnnotatedValue(identifier, sc.getType(), Kind.CLASS, sc);
    }

    protected AnnotatedValue getAnnotatedValue(Local local) {
        SootMethod sm = visitorState.getSootMethod();
        String identifier = sm.getSignature() + "@" + local.toString();
        AnnotatedValue ret = getAnnotatedValue(identifier, local.getType(), Kind.LOCAL, local);
        return ret;
    }

    protected AnnotatedValue getAnnotatedValue(Constant c) {
        SootClass sc = visitorState.getSootClass();
        String identifier = sc.getName() + "@" + c.toString();
        AnnotatedValue ret = getAnnotatedValue(identifier, c.getType(), Kind.LITERAL, c);
        return ret;
    }

    protected AnnotatedValue getAnnotatedValue(Value v) {
        if (v instanceof Local)
            return getAnnotatedValue((Local) v);
        else if (v instanceof Constant) 
            return getAnnotatedValue((Constant) v);
        else
            throw new RuntimeException("Not implemented for " + v.getClass());
    }

    protected AnnotatedValue getAnnotatedField(SootField field) {
        field = getDeclaringField(field);
        String identifier = field.getSignature();
        AnnotatedValue ret = annotatedValues.get(identifier);
        if (ret == null) {
            ret = new AnnotatedValue(identifier, field.getType(), Kind.FIELD, field);
            ret.setEnclosingClass(field.getDeclaringClass());
            ret.setEnclosingMethod(null);
            annotatedValues.put(identifier, ret);
        }
        if (!isAnnotated(ret)) {
            ret.setAnnotations(getVisibilityTags(field, Kind.FIELD), this);
            annotateField(ret, field);
        }
        return ret;
    }

    protected AnnotatedValue getAnnotatedParameter(SootMethod sm, int index) {
        if (index < 0 || index >= sm.getParameterCount())
            return null;

        sm = getDeclaringMethod(sm);

        String identifier = (isLibraryMethod(sm) ? LIB_PREFIX : "") + sm.getSignature() + "@parameter" + index;
        AnnotatedValue ret = annotatedValues.get(identifier);
        if (ret == null) {
            ret = new AnnotatedValue(identifier, sm.getParameterType(index), Kind.PARAMETER, sm);
            ret.setEnclosingClass(sm.getDeclaringClass());
            ret.setEnclosingMethod(sm);
            annotatedValues.put(identifier, ret);
        }
        if (!isAnnotated(ret)) {
            ret.setAnnotations(getVisibilitParameterTags(sm, index), this);
            annotateParameter(ret, sm, index);
        }
        return ret;
    }

    protected AnnotatedValue getAnnotatedReturn(SootMethod sm) {
        sm = getDeclaringMethod(sm);
        String identifier = (isLibraryMethod(sm) ? LIB_PREFIX : "") + sm.getSignature() + "@return";
        AnnotatedValue ret = annotatedValues.get(identifier);
        if (ret == null) {
            ret = new AnnotatedValue(identifier, sm.getReturnType(), Kind.RETURN, sm);
            ret.setEnclosingClass(sm.getDeclaringClass());
            ret.setEnclosingMethod(sm);
            annotatedValues.put(identifier, ret);
        }
        if (!isAnnotated(ret)) {
            ret.setAnnotations(getVisibilityTags(sm, Kind.RETURN), this);
            annotateReturn(ret, sm);
        }
        return ret;
    }

    protected AnnotatedValue getAnnotatedThis(SootMethod sm) {
        sm = getDeclaringMethod(sm);
        String identifier = (isLibraryMethod(sm) ? LIB_PREFIX : "") + sm.getSignature() + "@this";
        AnnotatedValue ret = annotatedValues.get(identifier);
        if (ret == null) {
            ret = new AnnotatedValue(identifier, sm.getDeclaringClass().getType(), Kind.THIS, sm);
            // TODO: this can also be annotated
            ret.setEnclosingClass(sm.getDeclaringClass());
            ret.setEnclosingMethod(sm);
            annotatedValues.put(identifier, ret);
        }
        if (!isAnnotated(ret)) {
            ret.setAnnotations(getVisibilityTags(sm, Kind.THIS), this);
            annotateThis(ret, sm);
        }
        return ret;
    }

	protected void addSubtypeConstraint(AnnotatedValue sub, AnnotatedValue sup) {
        if (sub.getKind() == Kind.LITERAL || sup.getKind() == Kind.LITERAL)
            return;
        Constraint c = new SubtypeConstraint(sub, sup);
        if (!constraints.add(c))
            return;
        addComponentConstraints(sub, sup);
	}

	protected void addEqualityConstraint(AnnotatedValue sub, AnnotatedValue sup) {
        if (sub.getKind() == Kind.LITERAL || sup.getKind() == Kind.LITERAL)
            return;
        Constraint c = new EqualityConstraint(sub, sup);
        if (!constraints.add(c))
            return;
        addComponentConstraints(sub, sup);
	}

    private void addComponentConstraints(AnnotatedValue sub, AnnotatedValue sup) {
        if (sub.getType() instanceof ArrayType && sup instanceof AdaptValue) {
            sup = ((AdaptValue) sup).getDeclValue();
        } else if (sub instanceof AdaptValue && sup.getType() instanceof ArrayType)
            sub = ((AdaptValue) sub).getDeclValue();

        if (sub.getType() instanceof ArrayType && sup.getType() instanceof ArrayType) {
            AnnotatedValue subComponent = getAnnotatedValue(sub.getIdentifier() + "[]", 
                    ((ArrayType) sub.getType()).getElementType(), Kind.COMPONENT, null);
            AnnotatedValue supComponent = getAnnotatedValue(sup.getIdentifier() + "[]", 
                    ((ArrayType) sup.getType()).getElementType(), Kind.COMPONENT, null);
            addEqualityConstraint(subComponent, supComponent);
        } 
    }

    protected void processMethod(SootMethod sm) {
        // Add override constraints
        if (sm.getName().equals("<init>") || sm.getName().equals("<clinit>"))
            return;
        Map<SootClass, SootMethod> overriddenMethods = InferenceUtils.overriddenMethods(sm);
        for (SootMethod overridden : overriddenMethods.values()) {
            handleMethodOverride(sm, overridden);
        }
    }

    protected SootField getDeclaringField(SootField field) {
        if (!field.isPhantom())
            return field;
        SootClass sc = field.getDeclaringClass();
        Set<SootClass> superTypes = InferenceUtils.getSuperTypes(sc);
        for (SootClass superClass : superTypes) {
            if (superClass.declaresField(field.getSubSignature())) {
                SootField f = superClass.getField(field.getSubSignature());
                if (!f.isPhantom())
                    return f;
            }
        }
        return field;
    }

    protected SootMethod getDeclaringMethod(SootMethod method) {
        if (!method.isPhantom())
            return method;
        SootClass sc = method.getDeclaringClass();
        Set<SootClass> superTypes = InferenceUtils.getSuperTypes(sc);
        for (SootClass superClass : superTypes) {
            if (superClass.declaresMethod(method.getSubSignature())) {
                SootMethod m = superClass.getMethod(method.getSubSignature());
                if (!m.isPhantom())
                    return m;
            }
        }
        return method;
    }

    protected void annotateDefault(AnnotatedValue v, Kind kind, Object o) {
    }

    protected void annotateArrayComponent(AnnotatedValue v, Object o) {
    }

    protected void annotateField(AnnotatedValue v, SootField field) {
    }

    protected void annotateThis(AnnotatedValue v, SootMethod method) {
    }

    protected void annotateParameter(AnnotatedValue v, SootMethod method, int index) {
    }

    protected void annotateReturn(AnnotatedValue v, SootMethod method) {
    }

    protected Set<Annotation> getVisibilitParameterTags(Host host, int index) {
        Set<Annotation> annos = AnnotationUtils.createAnnotationSet();
        VisibilityParameterAnnotationTag ptag = (VisibilityParameterAnnotationTag)
            host.getTag("VisibilityParameterAnnotationTag");
        VisibilityAnnotationTag vtag = null;
        if (ptag != null && index < ptag.getVisibilityAnnotations().size() 
                && (vtag = ptag.getVisibilityAnnotations().get(index)) != null
                && vtag.hasAnnotations()) {
            for (AnnotationTag at : vtag.getAnnotations()) {
                Annotation anno = AnnotationUtils.fromAnnotationTag(at);
                if (anno != null)
                    annos.add(anno);
            }
        }
        Set<Annotation> srcAnnos = getSourceLevelQualifiers();
        annos.retainAll(srcAnnos);
        return annos;
    }

    protected Set<Annotation> getVisibilityTags(Host host, Kind kind) {
        Set<Annotation> annos = getRawVisibilityTags(host);
        Set<Annotation> set = AnnotationUtils.createAnnotationSet(); 
        for (Iterator<Annotation> it = annos.iterator(); it.hasNext();) {
            Annotation anno = it.next();
            if (anno.toString().endsWith("This")) {
                it.remove();
                if (kind == Kind.THIS) {
                    String name = anno.annotationType().getCanonicalName();
                    set.add(AnnotationUtils.fromName(name.substring(0, name.length() - 4)));
                }
            }
            else if (kind == Kind.THIS)
                it.remove();
        }
        annos.addAll(set);
        Set<Annotation> srcAnnos = getSourceLevelQualifiers();
        annos.retainAll(srcAnnos);
        return annos;
    }

    /**
     * Get all original annotations without filtering 
     */
    protected Set<Annotation> getRawVisibilityTags(Host host) {
        Set<Annotation> annos = AnnotationUtils.createAnnotationSet();
        VisibilityAnnotationTag vtag = (VisibilityAnnotationTag) 
            host.getTag("VisibilityAnnotationTag");
        if (vtag != null && vtag.hasAnnotations()) {
            for (AnnotationTag at : vtag.getAnnotations()) {
                Annotation anno = AnnotationUtils.fromAnnotationTag(at);
                if (anno != null)
                    annos.add(anno);
            }
        }
        return annos;
    }

    public Set<Constraint> getConstraints() {
        return constraints;
    }

    public Map<String, AnnotatedValue> getAnnotatedValues() {
        return annotatedValues;
    }

    public void clear() {
        locals.clear();
        constraints.clear();
        visitedClasses.clear();
    }

    public boolean isLibraryMethod(SootMethod sm) {
        sm = getDeclaringMethod(sm);
        SootClass sc = sm.getDeclaringClass();
        return sc.isLibraryClass();
    }

    public boolean isFromLibrary(AnnotatedValue av) {
        Object o = av.getValue();
        if (o != null && o instanceof SootMethod && isLibraryMethod((SootMethod) o))
            return true;
        return false;
    }

    public void printJaif(PrintStream out) {
        for (SootClass sc : visitedClasses) {
            printJaifClass(sc, "", out);
        }
    }

    protected void printJaifClass(SootClass sc, String indent, PrintStream out) {
        out.println(indent + "package " + sc.getPackageName() + ":");
        out.println();
        out.println(indent + "class " + sc.getShortName() + ":");
        for (SootField sf : sc.getFields()) {
            printJaifField(sf, indent + "\t", out);
            out.println();
        }
        for (SootMethod sm : sc.getMethods()) {
            printJaifMethod(sm, indent + "\t", out);
            out.println();
        }
        out.println();
    }

    protected void printJaifMethod(SootMethod sm, String indent, PrintStream out) {
        out.println(indent + "method " + sm.getSubSignature() + ":");
        if (sm.getReturnType() != VoidType.v()) {
            printAnnotatedValue(getAnnotatedReturn(sm), "return", indent + "\t", out);
        }
        if (!sm.isStatic()) {
            printAnnotatedValue(getAnnotatedThis(sm), "receiver", indent + "\t", out);
        }
        indent += "\t";
        for (int i = 0; i < sm.getParameterCount(); i++) {
            out.println(indent + "parameter #" + i + ":");
            printAnnotatedValue(getAnnotatedParameter(sm, i), "type", indent + "\t", out);
        }
        // locals
        if (needLocals) {
            SootMethod prev = visitorState.getSootMethod();
            visitorState.setSootMethod(sm);
            try {
                Map<String, AnnotatedValue> map = locals.get(sm);
                if (map == null)
                    return;
                for (AnnotatedValue l : map.values()) {
                    out.println(indent + "local " + l.getName() + ":");
                    printAnnotatedValue(l, "type", indent + "\t", out);
                }
            } finally {
                visitorState.setSootMethod(prev);
            }
        }
    }

    protected void printJaifField(SootField sf, String indent, PrintStream out) {
        out.println(indent + "field " + sf.getName() + ":");
        printAnnotatedValue(getAnnotatedField(sf), "type", indent + "\t", out);
    }

    protected void printAnnotatedValue(AnnotatedValue av, String typeStr, String indent, PrintStream out) {
        out.println(indent + typeStr + ": " + av.getAnnotations(this) + " (" + av.getId() + ")");
        if (av.getType() instanceof ArrayType) {
            AnnotatedValue component = getAnnotatedValue(av.getIdentifier() + "[]", 
                    ((ArrayType) av.getType()).getElementType(), Kind.COMPONENT, null);
            printAnnotatedValue(component, "inner-type", indent + "\t", out);
        }
    }

    public Annotation adaptField(Annotation contextAnno, Annotation declAnno) {
//        ViewpointAdapter vp = getViewpointAdapter();
        return vpa.adaptField(contextAnno, declAnno);
    }
	
    public Annotation adaptMethod(Annotation contextAnno, Annotation declAnno) {
//        ViewpointAdapter vp = getViewpointAdapter();
        return vpa.adaptMethod(contextAnno, declAnno);
    }

	/**
	 * Adapt the declared type of a field from the point of view the receiver
	 * @param contextSet The set of annotations of the receiver type
	 * @param declSet The set of annotations of the declared type
	 * @return
	 */
	public Set<Annotation> adaptFieldSet(Set<Annotation> contextSet,
			Set<Annotation> declSet) {
        ViewpointAdapter vp = getViewpointAdapter();
		Set<Annotation> outSet = AnnotationUtils.createAnnotationSet();
		for (Annotation declAnno : declSet) {
			for (Annotation rcvAnno : contextSet) {
				Annotation anno = vp.adaptField(rcvAnno, declAnno);
				if (anno != null)
					outSet.add(anno);
			}
		}
		return outSet;
	}

	public Set<Annotation> adaptMethodSet(Set<Annotation> contextSet,
			Set<Annotation> declSet) {
        ViewpointAdapter vp = getViewpointAdapter();
		Set<Annotation> outSet = AnnotationUtils.createAnnotationSet();
		for (Annotation declAnno : declSet) {
			for (Annotation rcvAnno : contextSet) {
				Annotation anno = vp.adaptMethod(rcvAnno, declAnno);
				if (anno != null)
					outSet.add(anno);
			}
		}
		return outSet;
	}

    protected void handleMethodOverride(SootMethod overrider, SootMethod overridden) {
        // only handle overridden methods with active body?
        if (!overrider.isStatic()) {
            // this: overridden <: overrider 
            AnnotatedValue overriderThis = getAnnotatedThis(overrider);
            AnnotatedValue overriddenThis = getAnnotatedThis(overridden);
            addSubtypeConstraint(overriddenThis, overriderThis);
        }
        // parameter: overridden <: overrider 
        assert overrider.getParameterCount() == overridden.getParameterCount();
        for (int i = 0; i < overrider.getParameterCount(); i++) {
            AnnotatedValue overriderParam = getAnnotatedParameter(overrider, i);
            AnnotatedValue overriddenParam = getAnnotatedParameter(overridden, i);
            addSubtypeConstraint(overriddenParam, overriderParam);
        }
        if (overrider.getReturnType() != VoidType.v()) {
            // return: overrider <: overridden 
            AnnotatedValue overriderRet = getAnnotatedReturn(overrider);
            AnnotatedValue overriddenRet = getAnnotatedReturn(overridden);
            addSubtypeConstraint(overriderRet, overriddenRet);
        }
    }

    protected void handleInstanceFieldRead(AnnotatedValue aBase, 
            AnnotatedValue aField, AnnotatedValue aLhs) {
        AnnotatedValue afv = getFieldAdaptValue(aBase, aField, aLhs);
        addSubtypeConstraint(afv, aLhs);
    }

    protected void handleInstanceFieldWrite(AnnotatedValue aBase, 
            AnnotatedValue aField, AnnotatedValue aRhs) {
        AnnotatedValue afv = getFieldAdaptValue(aBase, aField, null);
        addSubtypeConstraint(aRhs, afv);
    }

    protected void handleStaticFieldRead(AnnotatedValue aField, AnnotatedValue aLhs) {
        addSubtypeConstraint(aField, aLhs);
    }

    protected void handleStaticFieldWrite(AnnotatedValue aField, AnnotatedValue aRhs) {
        addSubtypeConstraint(aRhs, aField);
    }

    protected void handleMethodCall(InvokeExpr v, AnnotatedValue assignTo) {
        SootMethod enclosingMethod = getVisitorState().getSootMethod();
        SootMethod invokeMethod = v.getMethod();
        String methodName = invokeMethod.getName();
        String superClassName;
        String className;
        // Author: Lindsey
        // this is to catch the start() run() fiasco, I think it is fixed now
        try {
            className = v.getMethodRef().declaringClass().getName();
            superClassName = v.getMethodRef().declaringClass().getSuperclass().getName();
        } catch(RuntimeException e) {
            // The class has no superclass
            superClassName = "";
            className = "";
        }
        /*if(threadFixTable != null) {
            for(Map.Entry<Integer, List<Integer>> entry : threadFixTable.entrySet()) {
                int key = entry.getKey();
                List<Integer> value = entry.getValue();
                for (int i = 0; i < value.size(); i++) {
                        System v.getMethod().getDeclaringClass().hashCode()) {
                        System.out.println(String.format("THREADFIX: GOT IT (MAYBE): %s --> %s", className, methodName));
                    }
                }
            }
        }*/
        if(v.getMethod().getDeclaringClass().implementsInterface(RUNNABLE_CLASS)) {
            System.out.println(String.format("THREADFIX: current name: %s --> %s", v.getMethod().retrieveActiveBody().getThisLocal().getName(), v.getMethod().getDeclaringClass().getName()));
        }
        if(superClassName.equals(THREAD_CLASS) || className.equals(THREAD_CLASS)) {

            if(methodName.equals(START_METHOD) && !className.equals(THREAD_CLASS)) {
                invokeMethod = v.getMethodRef().declaringClass().getMethodByName(RUN_METHOD);
            }
            else if(className.equals(THREAD_CLASS) && superClassName.equals(OBJ_CLASS) && methodName.equals(START_METHOD)) {
                /*if(threadFixTable == null) {
                    threadFixTable = new HashMap<>();
                }
                if(invokeMethod.isConstructor()) {
                    /*List<String> tmpList = new ArrayList<>();
                    List<Type> paramList = v.getMethod().getParameterTypes();
                    int paramCount = v.getMethod().getParameterCount();
                    System.out.println(String.format("THREADFIX: PARAM COUNT: %d", paramCount));
                    for(int i = 0; i < paramCount; i++) {
                        String name = v.getMethod().retrieveActiveBody().getParameterLocal(i).getName();
                        System.out.println("THREADFIX: test: " + name);
                        tmpList.add(name);
                    }
                    threadFixTable.put(v.hashCode(), tmpList);
                    if(v.getMethod().hasActiveBody()) {
                        System.out.println(String.format("THREADFIX: %s has an active body.", v.getMethod().getName()));
                        List<Value> localVariables = v.getMethod().getActiveBody().getParameterRefs();
                        Iterator itr = localVariables.iterator();
                        int i = 0;
                        while(itr.hasNext()) {
                            Value value = (Value)itr.next();
                            // System.out.println(String.format("THREADFIX: value #%d --> %s", i, value.get));
                            i++;
                        }
                    }
                }
                System.out.println(String.format("THREADFIX: METHOD HASH: %d", v.hashCode()));
                System.out.println(String.format("THREADFIX: %s --> %S", v.getMethodRef().getSubSignature(), v.getMethod().getName()));
                System.out.println("THREADFIX: Method name: '" + v.getMethod().getName() + "'");
                System.out.println("THREADFIX: assignTo --> " + assignTo.getName()); */
                for(Map.Entry<Integer, SootMethod> entry : threadFixTable.entrySet()) {
                    int key = entry.getKey();
                    SootMethod value = entry.getValue();
                    System.out.println(String.format("THREADFIX: GOT IT (MAYBE): %d --> %d", v.getMethod().hashCode(), value.hashCode()));
                }
            }
        }
        AnnotatedValue aBase = null;
        if (v instanceof InstanceInvokeExpr) {
            // receiver
            InstanceInvokeExpr iv = (InstanceInvokeExpr) v;
            Value base = iv.getBase();
            aBase = getAnnotatedValue(base);
            AnnotatedValue aThis = getAnnotatedThis(invokeMethod);
            addSubtypeConstraint(aBase, getMethodAdaptValue(aBase, aThis, assignTo));
        }
        // parameters
        List<Value> args = v.getArgs();
        for (int i = 0; i < v.getArgCount(); i++) {
            Value arg = args.get(i);
            assert arg instanceof Local;
            AnnotatedValue aArg = getAnnotatedValue(arg);
            AnnotatedValue aParam = getAnnotatedParameter(invokeMethod, i);
            SootClass encClass = aParam.getEnclosingClass();
            SootMethod encMethod = aParam.getEnclosingMethod();
            if(encClass.getName().equals(THREAD_CLASS) && encMethod.isConstructor()) {
                if(threadFixTable == null) {
                    threadFixTable = new HashMap<>();
                }
                System.out.println("THREADFIX: ------------> " + encClass.getName() + " " + encMethod.getName());
                System.out.println("THREADFIX: ------------> " + aParam.getName());
                try {
                    SootMethod sootMethod = encClass.getMethodByName("run");
                    threadFixTable.put(v.getMethod().getDeclaringClass().getMethodByName("start").hashCode(), sootMethod);

                }
                catch (RuntimeException rte) {
                    System.out.println("Run time exception: " + rte.getMessage());
                }
            }
            addSubtypeConstraint(aArg, getMethodAdaptValue(aBase, aParam, assignTo));
        }
        // return
        if (invokeMethod.getReturnType() != VoidType.v()) {
            if (assignTo == null)
                throw new RuntimeException("Null assignTo");
            AnnotatedValue aReturn = getAnnotatedReturn(invokeMethod);
            addSubtypeConstraint(getMethodAdaptValue(aBase, aReturn, assignTo), assignTo);
        }
    }


    @Override
    protected void internalTransform(final Body b, String phaseName, 
            @SuppressWarnings("rawtypes") Map options) {
        SootMethod sm = b.getMethod();
        SootClass sc = (sm == null ? null : sm.getDeclaringClass());
        visitorState.setSootMethod(sm);
        visitorState.setSootClass(sc);
        visitedClasses.add(sc);
        processMethod(sm);
        InferenceVisitor visitor = getInferenceVisitor(this);

        final PatchingChain<Unit> units = b.getUnits();
        for(Iterator<Unit> iter = units.snapshotIterator(); iter.hasNext();) {
            final Unit u = iter.next();
            visitorState.setUnit(u);
            u.apply(visitor);
        }
        visitorState.setSootMethod(null);
        visitorState.setSootClass(null);
        visitorState.setUnit(null);

        if (!needLocals && phaseName.equals("jtp.sflow")) {
            locals.remove(sm);
        }
        adaptValues.clear();

    }
}
