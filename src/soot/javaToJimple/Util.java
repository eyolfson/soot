package soot.javaToJimple;

import java.util.*;

public class Util {
   

    public static String getSourceFileOfClass(soot.SootClass sootClass){
        String name = sootClass.getName();
        int index = name.indexOf("$");
        
        // inner classes are found in the very outer class
        if (index != -1){
            name = name.substring(0, index);
        }
        return name;
    }
    
    public static void addLnPosTags(soot.tagkit.Host host, polyglot.util.Position pos) {
        if (pos != null) {
            addLnPosTags(host, pos.line(), pos.endLine(), pos.column(), pos.endColumn()); 
        }
    }
    
    public static void addLnPosTags(soot.tagkit.Host host, int sline, int eline, int spos, int epos) {
        if (soot.options.Options.v().keep_line_number()){
            host.addTag(new soot.tagkit.SourceLnPosTag(sline, eline, spos, epos));
        }
    }
    
    /**
     * Position Tag Adder
     */
    public static void addPosTag(soot.tagkit.Host host, polyglot.util.Position pos) {
        if (pos != null) {
            addPosTag(host, pos.column(), pos.endColumn());
        }
    }

    public static void addMethodPosTag(soot.tagkit.Host meth, int start, int end){
    
        meth.addTag(new soot.tagkit.SourcePositionTag(start, end));
    }
    
    /**
     * Position Tag Adder
     */
    public static void addPosTag(soot.tagkit.Host host, int sc, int ec) {

        host.addTag(new soot.tagkit.SourcePositionTag(sc, ec));
    }

    public static void addMethodLineTag(soot.tagkit.Host host, int sline, int eline){
        if (soot.options.Options.v().keep_line_number()){
            host.addTag(new soot.tagkit.SourceLineNumberTag(sline, eline));    
        }
    }
    
    /**
     * Line Tag Adder
     */
    public static void addLineTag(soot.tagkit.Host host, polyglot.ast.Node node) {

        if (soot.options.Options.v().keep_line_number()){
            if (node.position() != null) {
                host.addTag(new soot.tagkit.SourceLineNumberTag(node.position().line(), node.position().line()));
                
            }
        }
    }
    
    /**
     * Line Tag Adder
     */
    public static void addLineTag(soot.tagkit.Host host, int sLine, int eLine) {

        host.addTag(new soot.tagkit.SourceLineNumberTag(sLine, eLine));
                    
    }
    
    public static soot.Local getThis(soot.Type sootType, soot.Body body, HashMap getThisMap, LocalGenerator lg){

        // if this for type already created return it from map
        if (getThisMap.containsKey(sootType)){
            return (soot.Local)getThisMap.get(sootType);
        }
        //System.out.println("getThis: type: "+sootType);
        //System.out.println("special this local type: "+specialThisLocal.getType());
        soot.Local specialThisLocal = body.getThisLocal();
        // if need this just return it
        if (specialThisLocal.getType().equals(sootType)) {
            //System.out.println("can just return this");
            getThisMap.put(sootType, specialThisLocal);
            return specialThisLocal;
        }
        
        // otherwise get this$0 for one level up
        soot.SootClass classToInvoke = ((soot.RefType)specialThisLocal.getType()).getSootClass();
        soot.SootField outerThisField = classToInvoke.getFieldByName("this$0");
        //System.out.println("outer This field: "+outerThisField);
        soot.Local t1 = lg.generateLocal(outerThisField.getType());
        
        soot.jimple.FieldRef fieldRef = soot.jimple.Jimple.v().newInstanceFieldRef(specialThisLocal, outerThisField);
        soot.jimple.AssignStmt fieldAssignStmt = soot.jimple.Jimple.v().newAssignStmt(t1, fieldRef);
        body.getUnits().add(fieldAssignStmt);
        
        if (t1.getType().equals(sootType)){
            //System.out.println("can just return this$0 field");
            getThisMap.put(sootType, t1);
            return t1;            
        }
        
        // otherwise make a new access method
        soot.Local t2 = t1;

        return getThisGivenOuter(sootType, getThisMap, body, lg, t2);
    }

    public static soot.Local getThisGivenOuter(soot.Type sootType, HashMap getThisMap, soot.Body body, LocalGenerator lg, soot.Local t2){
        
        while (!t2.getType().equals(sootType)){
            //System.out.println("t2 type: "+t2.getType());
            soot.SootClass classToInvoke = ((soot.RefType)t2.getType()).getSootClass();
            // make an access method and add it to that class for accessing 
            // its private this$0 field
            soot.SootMethod methToInvoke = makeOuterThisAccessMethod(classToInvoke);
            
            // generate a local that corresponds to the invoke of that meth
            soot.Local t3 = lg.generateLocal(methToInvoke.getReturnType());
            ArrayList methParams = new ArrayList();
            methParams.add(t2);
            soot.Local res = getPrivateAccessFieldInvoke(methToInvoke, methParams, body, lg);
            soot.jimple.AssignStmt assign = soot.jimple.Jimple.v().newAssignStmt(t3, res);
            body.getUnits().add(assign);
            //System.out.println("t3 type: "+t3.getType());
            t2 = t3;
            //System.out.println("created acces meth and t2's type is: "+t2.getType());
        }
            
        getThisMap.put(sootType, t2);

        return t2;        
    }
    

    private static soot.SootMethod makeOuterThisAccessMethod(soot.SootClass classToInvoke){
        String name = "access$"+soot.javaToJimple.InitialResolver.v().getNextPrivateAccessCounter()+"00";
        ArrayList paramTypes = new ArrayList();
        paramTypes.add(classToInvoke.getType());
        
        soot.SootMethod meth = new soot.SootMethod(name, paramTypes, classToInvoke.getFieldByName("this$0").getType(), soot.Modifier.STATIC);

        classToInvoke.addMethod(meth);
        PrivateFieldAccMethodSource src = new PrivateFieldAccMethodSource();
        src.fieldName("this$0");
        src.fieldType(classToInvoke.getFieldByName("this$0").getType());
        meth.setActiveBody(src.getBody(meth, null));
        return meth;
    }
    
    public static soot.Local getPrivateAccessFieldInvoke(soot.SootMethod toInvoke, ArrayList params, soot.Body body, LocalGenerator lg){
        soot.jimple.InvokeExpr invoke = soot.jimple.Jimple.v().newStaticInvokeExpr(toInvoke, params);

        soot.Local retLocal = lg.generateLocal(toInvoke.getReturnType());

        soot.jimple.AssignStmt stmt = soot.jimple.Jimple.v().newAssignStmt(retLocal, invoke);
        body.getUnits().add(stmt);

        return retLocal;
    }

    
    /**
     * Type handling
     */
    public static soot.Type getSootType(polyglot.types.Type type) {
		
		soot.Type sootType = null;
	
		if (type.isInt()){
			sootType = soot.IntType.v();
		}
		else if (type.isArray()){

            polyglot.types.Type polyglotBase = ((polyglot.types.ArrayType)type).base();
            while (polyglotBase instanceof polyglot.types.ArrayType) {
              polyglotBase = ((polyglot.types.ArrayType)polyglotBase).base();
            }
			soot.Type baseType = getSootType(polyglotBase);
			int dims = ((polyglot.types.ArrayType)type).dims();

            // do something here if baseType is still an array
			sootType = soot.ArrayType.v(baseType, dims);
		}
		else if (type.isBoolean()){
			sootType = soot.BooleanType.v();
		}
		else if (type.isByte()){
			sootType = soot.ByteType.v();
		}
		else if (type.isChar()){
			sootType = soot.CharType.v();
		}
		else if (type.isDouble()){
			sootType = soot.DoubleType.v();
		}
		else if (type.isFloat()){
			sootType = soot.FloatType.v();
		}
		else if (type.isLong()){
			sootType = soot.LongType.v();
		}
		else if (type.isShort()){
			sootType = soot.ShortType.v();
		}
		else if (type.isNull()){
			sootType = soot.NullType.v();
		}
		else if (type.isVoid()){
			sootType = soot.VoidType.v();
		}
		else if (type.isClass()){
            polyglot.types.ClassType classType = (polyglot.types.ClassType)type;
            String className;
            if (classType.isNested()) {
                if (classType.isAnonymous()) {
                    className = (String)soot.javaToJimple.InitialResolver.v().getAnonTypeMap().get(new polyglot.util.IdentityKey(classType));   
                }
                else if (classType.isLocal()) {
                    className = (String)soot.javaToJimple.InitialResolver.v().getLocalTypeMap().get(new polyglot.util.IdentityKey(classType));    
                }
                else {
                    String fullName = classType.fullName();
                    String pkgName = "";
                    if (classType.package_() != null){
                        pkgName = classType.package_().fullName();
                    }
                    className = classType.name();
                    
                    if (classType.outer().isAnonymous() || classType.outer().isLocal()){
                        className = getSootType(classType.outer()).toString()+"$"+className;
                    }
                    else {
                        while (classType.outer() != null){
                            className = classType.outer().name()+"$"+className;
                            classType = classType.outer();
                        }

                        if (!pkgName.equals("")){
                            className = pkgName+"."+className;
                        }
                    }
                }
            }
            else {
			    className = classType.fullName();
            }
            
			sootType = soot.RefType.v(className);
		}
		else{
			throw new RuntimeException("Unknown Type");
		}
		return sootType;
    }    
    
    
    /**
     * Modifier Creation
     */
	public static int getModifier(polyglot.types.Flags flags) {

		int modifier = 0;
		
		if (flags.isPublic()){
			modifier = modifier | soot.Modifier.PUBLIC;	
		}
		if (flags.isPrivate()){
			modifier = modifier | soot.Modifier.PRIVATE;
		}
		if (flags.isProtected()){
			modifier = modifier | soot.Modifier.PROTECTED;
		}
		if (flags.isFinal()){
			modifier = modifier | soot.Modifier.FINAL;
		}
		if (flags.isStatic()){
			modifier = modifier | soot.Modifier.STATIC;
		}
		if (flags.isNative()){
			modifier = modifier | soot.Modifier.NATIVE;
		}
		if (flags.isAbstract()){
			modifier = modifier | soot.Modifier.ABSTRACT;
		}
		if (flags.isVolatile()){
			modifier = modifier | soot.Modifier.VOLATILE;
		}
		if (flags.isTransient()){
			modifier = modifier | soot.Modifier.TRANSIENT;
		}
		if (flags.isSynchronized()){
			modifier = modifier | soot.Modifier.SYNCHRONIZED;
		}
		if (flags.isInterface()){
			modifier = modifier | soot.Modifier.INTERFACE;
		}

		return modifier;
	}
}
