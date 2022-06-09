package rs.ac.bg.etf.pp1;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import org.apache.log4j.Logger;

import rs.ac.bg.etf.pp1.ast.*;
import rs.etf.pp1.symboltable.*;
import rs.etf.pp1.symboltable.concepts.*;
import rs.etf.pp1.symboltable.structure.*;

public class SemanticPass extends VisitorAdaptor {
	
	int nVars;
	boolean errorDetected = false;
	Logger log = Logger.getLogger(RuleVisitor.class);
	
	public boolean passed() {
		return !errorDetected;
	}
	
	public void report_error(String message, SyntaxNode info) {
		errorDetected = true;
		StringBuilder msg = new StringBuilder(message);
		int line = (info == null) ? 0 : info.getLine();
		if (line != 0)
			msg.append(" na liniji ").append(line);
		log.error(msg.toString());
	}
	
	public void report_info(String message, SyntaxNode info) {
		StringBuilder msg = new StringBuilder(message);
		int line = (info == null) ? 0 : info.getLine();
		if (line != 0)
			msg.append(" na liniji ").append(line);
		log.info(msg.toString());
	}
	
	private int currentLevel = -1;
	private Type currentType = null; // Stores the type of a current variable/array/method
	private Obj currentClass = null;
	private MethodName currentMethod = null;
	private boolean doesCurrentMethodOverride = false;
	private SymbolDataStructure currentClassObjs = null;
	private Stack<List<Obj>> functionFormalParams = new Stack<>();
	private Stack<List<Expr>> functionActualParams = new Stack<>();
	private boolean returnFound = false;
	/*
	- > 0: Stores the level of a do while loop the program is inside of (do while loops can be nested)
	- == 0: Program is outside of the do while loop
	*/
	private int insideDoWhileLoop = 0;
	// caseSets is made to check whether or not there are multiple cases with the same number inside of one switch statement
	// Since switch statements can be nested, we need to have a stack of sets storing the case numbers for each switch statement respectively
	private Stack<Set<Integer>> caseSets = new Stack<>();
	
	public static final Struct boolType = new Struct(Struct.Bool);
	public SemanticPass() {
		Tab.currentScope().addToLocals(new Obj(Obj.Type, "bool", SemanticPass.boolType));
		// Setting predefined functions' level to 0 and their arguments' number
		Tab.chrObj.setLevel(0);
		Tab.ordObj.setLevel(0);
		Tab.lenObj.setLevel(0);
		Tab.chrObj.getLocalSymbols().iterator().next().setFpPos(1);
		Tab.ordObj.getLocalSymbols().iterator().next().setFpPos(1);
		Tab.lenObj.getLocalSymbols().iterator().next().setFpPos(1);
	}
	
	public void visit(Program program) {
		// Check if main exists - To be implemented
		checkIfMainExists();
		nVars = Tab.currentScope().getnVars();
		Tab.chainLocalSymbols(program.getProgName().obj);
		Tab.closeScope();
		currentLevel--;
	}
	
	private void checkIfMainExists() {
		Obj mainObj = Tab.currentScope().findSymbol("main");
		if (mainObj == null) {
			report_error("Nije nadjena funkcija main!",null);
			return;
		}
		if (mainObj.getType().getKind() != Struct.None) {
			report_error("Funkcija main mora biti tipa void!", null);
			return;
		}
		List<Obj> mainParams = getFunctionParams(mainObj);
		if (mainParams.size() > 0)
			report_error("Funkcija main ne sme imati nikakve parametre!", null);
	}
	
	private List<Obj> getFunctionParams(Obj functionObj) {
		List<Obj> functionParams = new ArrayList<>();
		for (Obj obj : functionObj.getLocalSymbols()) {
			if (obj.getFpPos() == 0) continue; // If fpPos == 0, obj is either parameter this or a local variable!
			functionParams.add(obj);
		}
		return functionParams;
	}
	
	public void visit(ProgName progName) {
		progName.obj = Tab.insert(Obj.Prog, progName.getProgName(), Tab.noType);
		progName.obj.setLevel(currentLevel);
		Tab.openScope();
		currentLevel++;
	}
	
	public void visit(Type type) {
		Obj identTypeNode = Tab.find(type.getTypeName());
		if (identTypeNode == Tab.noObj) {
			report_error("Nije pronadjen tip " + type.getTypeName() + " u tabeli simbola!", type);
			type.struct = Tab.noType;
		}
		else
			if (identTypeNode.getKind() == Obj.Type)
				type.struct = identTypeNode.getType();
			else {
				report_error("Greska: Ime " + type.getTypeName() + " ne predstavlja tip!", type);
				type.struct = Tab.noType;
			}
		currentType = type;
	}
	
	public void visit(ConstNumIdent constNumIdent) {
		if (Tab.currentScope().findSymbol(constNumIdent.getConstName()) != null)  {
			report_error("Greska: Ime " + constNumIdent.getConstName() + " je vec deklarisano u trenutnom opsegu!", constNumIdent);
			return;
		}
		Obj constNode = Tab.insert(Obj.Con, constNumIdent.getConstName(), currentType.struct);
		if (currentType.struct.getKind() != Struct.Int) {
			report_error("Nedozvoljena dodela vrednosti nenumerickoj konstanti (konstanta sa leve strane nije tipa int)!", constNumIdent);
			return;
		}
		constNode.setAdr(constNumIdent.getNum());
		constNode.setLevel(currentLevel);
	}
	
	public void visit(ConstCharIdent constCharIdent) {
		if (Tab.currentScope().findSymbol(constCharIdent.getConstName()) != null) {
			report_error("Greska: Ime " + constCharIdent.getConstName() + " je vec deklarisano u trenutnom opsegu!", constCharIdent);
			return;
		}
		Obj constNode = Tab.insert(Obj.Con, constCharIdent.getConstName(), currentType.struct);
		if (currentType.struct.getKind() != Struct.Char) {
			report_error("Nedozvoljena dodela vrednosti nekarakternoj konstanti (konstanta sa leve strane nije tipa char)!", constCharIdent);
			return;
		}
		constNode.setAdr(constCharIdent.getCh());
		constNode.setLevel(currentLevel);
	}
	
	public void visit(ConstBoolIdent constBoolIdent) {
		if (Tab.currentScope().findSymbol(constBoolIdent.getConstName()) != null) {
			report_error("Greska: Ime " + constBoolIdent.getConstName() + " je vec deklarisano u trenutnom opsegu!", constBoolIdent);
			return;
		}
		Obj constNode = Tab.insert(Obj.Con, constBoolIdent.getConstName(), currentType.struct);
		if (currentType.struct.getKind() != Struct.Bool) {
			report_error("Nedozvoljena dodela vrednosti nelogickoj konstanti (konstanta sa leve strane nije tipa bool)!", constBoolIdent);
			return;
		}
		constNode.setAdr(constBoolIdent.getBool().equals("true") ? 1 : 0);
		constNode.setLevel(currentLevel);
	}
	
	public void visit(ClassDecl classDecl) {
		Tab.chainLocalSymbols(classDecl.getClassName().obj.getType());
		Tab.closeScope();
		currentLevel--;
		currentClass = null;
		currentClassObjs = null;
	}
	
	public void visit(BaseClassName baseClassName) {
		baseClassName.obj = Tab.insert(Obj.Type, baseClassName.getClassName(),
				new Struct(Struct.Class, new HashTableDataStructure()));
		currentClass = baseClassName.obj;
		currentClassObjs = new HashTableDataStructure();
		Tab.openScope();
		currentLevel++;
	}
	
	public void visit(DerivedClassName derivedClassName) {
		derivedClassName.obj = derivedClassName.getDerClassName().obj;
	}
	
	public void visit(DerClassName derClassName) {
		derClassName.obj = Tab.insert(Obj.Type, derClassName.getDerivedClassName(),
				new Struct(Struct.Class, new HashTableDataStructure()));
		currentClass = derClassName.obj;
		currentClassObjs = new HashTableDataStructure();
		Tab.openScope();
		currentLevel++;
	}
	
	public void visit(ExtendsClassName extendsClassName) {
		Obj classObj = Tab.find(extendsClassName.getBaseClassName());
		if (classObj == Tab.noObj) {
			report_error("Greska: Ne postoji tip " + extendsClassName.getBaseClassName(), extendsClassName);
			return;
		}
		if (classObj.getKind() != Obj.Type || classObj.getType().getKind() != Struct.Class) {
			report_error("Greska: " + extendsClassName.getBaseClassName() + " nije tip ili nije klasa!", extendsClassName);
			return;
		}
		currentClass.getType().addImplementedInterface(classObj.getType());
		// Inherit all the fields from the base class
		for (Obj obj : classObj.getType().getMembersTable().symbols()) {
			if (obj.getKind() != Obj.Fld) continue;
			Obj copyObj = Tab.insert(Obj.Fld, obj.getName(), obj.getType());
			copyObj.setAdr(obj.getAdr());
			currentClassObjs.insertKey(copyObj);
		}
	}
	
	public void visit(LBRACEAfterVarDeclList lBraceAfterVarDeclList) {
		// Inherit all the methods from the base class
		fillBaseClassMethods(lBraceAfterVarDeclList.getLine());
	}
	
	private void fillBaseClassMethods(int line) {
		Collection<Struct> implementedInterfaces = currentClass.getType().getImplementedInterfaces();
		if (implementedInterfaces.size() > 0) { // Current class is a derived one - add all non-overriden methods
			Iterator<Struct> iterator = implementedInterfaces.iterator();
			Struct baseClassStruct = iterator.next();
			for (Obj obj : baseClassStruct.getMembersTable().symbols()) {
				if (obj.getKind() != Obj.Meth) continue;
				Obj o = Tab.currentScope().findSymbol(obj.getName());
				if (o != null) 
					report_error("Greska: Ime " + obj.getName() + " vec postoji kao metoda u okviru osnovne klase! na liniji " + line, null);
				Obj baseClassMethod = Tab.insert(Obj.Meth, obj.getName(), obj.getType());
				baseClassMethod.setAdr(obj.getAdr());
				baseClassMethod.setFpPos(obj.getFpPos());
				baseClassMethod.setLevel(obj.getLevel());
				Tab.openScope();
				currentLevel++;
				Obj thisObj = Tab.insert(Obj.Var, "this", currentClass.getType());
				thisObj.setAdr(Tab.currentScope().getnVars() - 1);
				thisObj.setLevel(currentLevel);
				thisObj.setFpPos(0);
				for (Obj baseMethodLocal : obj.getLocalSymbols()) {
					Obj paramObj = Tab.insert(Obj.Var, baseMethodLocal.getName(), baseMethodLocal.getType());
					paramObj.setAdr(Tab.currentScope().getnVars() - 1);
					paramObj.setLevel(currentLevel);
					if (baseMethodLocal.getFpPos() != 0)
						paramObj.setFpPos(Tab.currentScope().getnVars());
				}
				Tab.chainLocalSymbols(baseClassMethod);
				Tab.closeScope();
				currentLevel--;
			}
		}
	}
	
	public void visit(VarIdent varIdent) {
		if (Tab.currentScope().findSymbol(varIdent.getVarName()) != null) {
			report_error("Greska: Ime " + varIdent.getVarName() + " je vec deklarisano u trenutnom opsegu!", varIdent);
			return;
		}
		Obj varNode = null;
		if (currentMethod != null) { // Local variable
			varNode = Tab.insert(Obj.Var, varIdent.getVarName(), currentType.struct);
			varNode.setLevel(currentLevel);
			varNode.setAdr(Tab.currentScope().getnVars() - 1);
		}
		else if (currentClass != null) { // Class field
			varNode = Tab.insert(Obj.Fld, varIdent.getVarName(), currentType.struct);
			int nVars = Tab.currentScope().getnVars();
			varNode.setAdr((nVars == 0) ? 1 : nVars); // Because of the TVF
			currentClassObjs.insertKey(varNode);
		}
		else { // Global varaible
			varNode = Tab.insert(Obj.Var, varIdent.getVarName(), currentType.struct);
			varNode.setAdr(Tab.currentScope().getnVars() - 1);
		}
	}
	
	public void visit(ArrIdent arrIdent) {
		if (Tab.currentScope().findSymbol(arrIdent.getArrName()) != null) {
			report_error("Greska: Ime " + arrIdent.getArrName() + " je vec deklarisano u trenutnom opsegu!", arrIdent);
			return;
		}
		Obj arrNode = null;
		if (currentMethod != null) { // Local variable
			arrNode = Tab.insert(Obj.Var, arrIdent.getArrName(), new Struct(Struct.Array, currentType.struct));
			arrNode.setLevel(currentLevel);
			arrNode.setAdr(Tab.currentScope().getnVars() - 1);
		}
		else if (currentClass != null) { // Class field
			arrNode = Tab.insert(Obj.Fld, arrIdent.getArrName(), new Struct(Struct.Array, currentType.struct));
			int nVars = Tab.currentScope().getnVars();
			arrNode.setAdr((nVars == 0) ? 1 : nVars); // Because of the TVF
			currentClassObjs.insertKey(arrNode);
		}
		else { // Global variable
			arrNode = Tab.insert(Obj.Var, arrIdent.getArrName(), new Struct(Struct.Array, currentType.struct));
			arrNode.setAdr(Tab.currentScope().getnVars() - 1);
		}
	}
	
	public void visit(MethodDecl methodDecl) {
		if (methodDecl.getMethodName().obj == Tab.noObj) return; // Error occurred
		if (methodDecl.getMethodName() instanceof RetMethodName && returnFound == false)
			report_error("Greska: return iskaz u okviru metode koja nije deklarisana kao void nije pronadjen!", methodDecl);
		Tab.chainLocalSymbols(methodDecl.getMethodName().obj);
		if (doesCurrentMethodOverride == true) {
			String name = null;
			if (methodDecl.getMethodName() instanceof RetMethodName)
				name = ((RetMethodName) methodDecl.getMethodName()).getMethodName();
			else // VoidMethodName
				name = ((VoidMethodName) methodDecl.getMethodName()).getMethodName();
			Obj baseMethodObj = currentClass.getType().getImplementedInterfaces().iterator().next().getMembersTable().searchKey(name);
			// A method that overrides must have the same amount of parameters of the same type - done in checkParams!
			checkParams(getFunctionParams(currentMethod.obj), getFunctionParams(baseMethodObj), methodDecl.getLine());
			doesCurrentMethodOverride = false;
		}
		Tab.closeScope();
		currentMethod = null;
		currentLevel--;
		returnFound = false;
	}
	
	private void checkParams(List<Obj> paramListA, List<Obj> paramListB, int line) {
		if (paramListA.size() != paramListB.size()) {
			report_error("Greska: Broj parametara metode koja nadjacava metodu osnovne klase mora biti isti kao i u metodi osnovne klase! na liniji " + line, null);
			return;
		}
		for (int i = 0; i < paramListA.size(); i++)
			if (areObjectsAssignable(paramListA.get(i).getType(), paramListB.get(i).getType()) == false &&
					paramListA.get(i).getType().compatibleWith(paramListB.get(i).getType()) == false)
				report_error("Greska: Parametri broj " + (i + 1) + " nisu istih tipova u metodi koja nadjacava i metodi osnovne klase! na liniji " + line, null);
	}
	
	// Implemented to support base class object being assigned with a derived class object
	private boolean areObjectsAssignable(Struct obj1, Struct obj2) {
		if (obj1.getKind() != Struct.Class && obj2.getKind() != Struct.Class) return false;
		for (Struct implementedInterface : obj2.getImplementedInterfaces())
			if (implementedInterface.equals(obj1) == true)
				return true;
		return false;
	}
	
	public void visit(RetMethodName retMethodName) {
		Obj obj = Tab.currentScope().findSymbol(retMethodName.getMethodName());
		if (obj != null) {
			if (currentClass == null) {
				report_error("Greska: Ime " + retMethodName.getMethodName() + " je vec deklarisano u trenutnom opsegu!", retMethodName);
				retMethodName.obj = Tab.noObj;
				return;
			}
			if (currentClass.getType().getImplementedInterfaces().size() == 0) {
				report_error("Greska: Ime " + retMethodName.getMethodName() + " je vec deklarisano u trenutnom opsegu!", retMethodName);
				retMethodName.obj = Tab.noObj;
				return;
			}
			if (obj.getKind() != Obj.Meth) {
				report_error("Greska: Ime " + retMethodName.getMethodName() + " je vec deklarisano u trenutnom opsegu!", retMethodName);
				retMethodName.obj = Tab.noObj;
				return;
			}
			// User is trying to override a base class method
			if (obj.getType() != currentType.struct) {
				report_error("Greska: Povratna vrednost metode koja se nadjacava mora biti istog tipa kao i metoda u osnovnoj klasi", retMethodName);
				retMethodName.obj = Tab.noObj;
				return;
			}
			retMethodName.obj = obj;
			retMethodName.obj.setLocals(new HashTableDataStructure());  // Reset parameters and local symbols
			currentMethod = retMethodName;
			Tab.openScope();
			currentLevel++;
			if (currentClass != null) {
				currentClassObjs.insertKey(retMethodName.obj);
				Obj thisObj = Tab.insert(Obj.Var, "this", currentClass.getType());
				thisObj.setAdr(Tab.currentScope().getnVars() - 1);
				thisObj.setLevel(currentLevel);
				thisObj.setFpPos(0);
			}
			doesCurrentMethodOverride = true;
		}
		else {
			retMethodName.obj = Tab.insert(Obj.Meth, retMethodName.getMethodName(), currentType.struct);
			retMethodName.obj.setLevel(currentLevel);
			currentMethod = retMethodName;
			Tab.openScope();
			currentLevel++;
			if (currentClass != null) {
				currentClassObjs.insertKey(retMethodName.obj);
				Obj thisObj = Tab.insert(Obj.Var, "this", currentClass.getType());
				thisObj.setAdr(Tab.currentScope().getnVars() - 1);
				thisObj.setLevel(currentLevel);
				thisObj.setFpPos(0);
			}
		}
	}
	
	public void visit(VoidMethodName voidMethodName) {
		Obj obj = Tab.currentScope().findSymbol(voidMethodName.getMethodName());
		if (obj != null) {
			if (currentClass == null) {
				report_error("Greska: Ime " + voidMethodName.getMethodName() + " je vec deklarisano u trenutnom opsegu!", voidMethodName);
				voidMethodName.obj = Tab.noObj;
				return;
			}
			if (currentClass.getType().getImplementedInterfaces().size() == 0) {
				report_error("Greska: Ime " + voidMethodName.getMethodName() + " je vec deklarisano u trenutnom opsegu!", voidMethodName);
				voidMethodName.obj = Tab.noObj;
				return;
			}
			if (obj.getKind() != Obj.Meth) {
				report_error("Greska: Ime " + voidMethodName.getMethodName() + " je vec deklarisano u trenutnom opsegu!", voidMethodName);
				voidMethodName.obj = Tab.noObj;
				return;
			}
			// User is trying to override a base class method
			if (obj.getType() != Tab.noType) {
				report_error("Greska: Povratna vrednost metode koja se nadjacava mora biti istog tipa kao i metoda u osnovnoj klasi", voidMethodName);
				voidMethodName.obj = Tab.noObj;
				return;
			}
			voidMethodName.obj = obj;
			obj.setLocals(new HashTableDataStructure());  // Reset parameters and local symbols
			currentMethod = voidMethodName;
			Tab.openScope();
			currentLevel++;
			if (currentClass != null) {
				currentClassObjs.insertKey(voidMethodName.obj);
				Obj thisObj = Tab.insert(Obj.Var, "this", currentClass.getType());
				thisObj.setAdr(Tab.currentScope().getnVars() - 1);
				thisObj.setLevel(currentLevel);
				thisObj.setFpPos(0);
			}
			doesCurrentMethodOverride = true;
		}
		else {
			voidMethodName.obj = Tab.insert(Obj.Meth, voidMethodName.getMethodName(), Tab.noType);
			voidMethodName.obj.setLevel(currentLevel);
			currentMethod = voidMethodName;
			Tab.openScope();
			currentLevel++;
			if (currentClass != null) {
				currentClassObjs.insertKey(voidMethodName.obj);
				Obj thisObj = Tab.insert(Obj.Var, "this", currentClass.getType());
				thisObj.setAdr(Tab.currentScope().getnVars() - 1);
				thisObj.setLevel(currentLevel);
				thisObj.setFpPos(0);
			}
		}
	}
	
	public void visit(VarParam varParam) {
		if (Tab.currentScope().findSymbol(varParam.getIdent()) != null) {
			report_error("Greska: Parametar sa imenom: " + varParam.getIdent() + " je vec deklarisan!", varParam);
			return;
		}
		Obj paramObj = Tab.insert(Obj.Var, varParam.getIdent(), currentType.struct);
		paramObj.setAdr(Tab.currentScope().getnVars() - 1);
		paramObj.setLevel(currentLevel);
		paramObj.setFpPos(Tab.currentScope().getnVars());
	}
	
	public void visit(ArrParam arrParam) {
		if (Tab.currentScope().findSymbol(arrParam.getIdent()) != null) {
			report_error("Greska: Parametar sa imenom: " + arrParam.getIdent() + " je vec deklarisan!", arrParam);
			return;
		}
		Obj paramObj = Tab.insert(Obj.Type, arrParam.getIdent(), new Struct(Struct.Array, currentType.struct));
		paramObj.setAdr(Tab.currentScope().getnVars() - 1);
		paramObj.setLevel(currentLevel);
		paramObj.setFpPos(Tab.currentScope().getnVars());
	}
	
	public void visit(UnmatchedIf unmatchedIf) {
		if (unmatchedIf.getCondition().struct != SemanticPass.boolType)
			report_error("Greska: Uslov u okviru if naredbe mora biti tipa bool!", unmatchedIf);
	}
	
	public void visit(UnmatchedIfElse unmatchedIfElse) {
		if (unmatchedIfElse.getCondition().struct != SemanticPass.boolType)
			report_error("Greska: Uslov u okviru if naredbe mora biti tipa bool!", unmatchedIfElse);
	}
	
	public void visit(DoWhileLoop doWhileLoop) {
		if (doWhileLoop.getCondition().struct != SemanticPass.boolType)
			report_error("Greska: Uslov u okviru do while petlje mora biti tipa bool!", doWhileLoop);
		insideDoWhileLoop--;
	}
	
	public void visit(SwitchStmt switchStmt) {
		if (switchStmt.getExpr().struct != Tab.intType)
			report_error("Greska: Izraz u okviru switch naredbe mora biti tipa int!", switchStmt);
		caseSets.pop();
	}
	
	public void visit(BreakStmt breakStmt) {
		if (insideDoWhileLoop == 0 && caseSets.size() == 0)
			report_error("Greska: break se mora naci unutar do while petlje ili case naredbe!", breakStmt);
	}
	
	public void visit(ContinueStmt continueStmt) {
		if (insideDoWhileLoop == 0)
			report_error("Greska: continue se mora naci unutar do while petlje!", continueStmt);
	}
	
	int printCallCount = 0;
	public void visit(PrintStmt printStmt) {
		Struct exprStruct = printStmt.getExpr().struct;
		if (exprStruct != Tab.intType && exprStruct != Tab.charType && exprStruct != SemanticPass.boolType) {
			report_error("Greska: Izraz u okviru print naredbe mora biti tipa int, char ili bool!", printStmt);
			return;
		}
		printCallCount++;
		log.info("Found print!");
	}
	
	public void visit(MultiplePrintStmts multiplePrintStmts) {
		Struct exprStruct = multiplePrintStmts.getExpr().struct;
		if (exprStruct != Tab.intType && exprStruct != Tab.charType && exprStruct != SemanticPass.boolType) {
			report_error("Greska: Izraz u okviru print naredbe mora biti tipa int, char ili bool!", multiplePrintStmts);
			return;
		}
		printCallCount++;
		log.info("Found print!");
	}
	
	public void visit(ReturnExpr returnExpr) {
		if (currentMethod == null) {
			report_error("Greska: return iskaz se mora naci unutar metode!", returnExpr);
			return;
		}
		returnFound = true;
		if (currentMethod.obj.getType().getKind() == Struct.None)
			report_error("Greska: return iskaz sa izrazom se ne sme naci u metodi definisanoj kao void!", returnExpr);
		else if (currentMethod.obj.getType().equals(returnExpr.getExpr().struct) == false)
			report_error("Greska: Izraz u okviru return iskaza mora biti istog tipa kao i povratna vrednost metode!", returnExpr);
	}
	
	public void visit(ReturnNoExpr returnNoExpr) {
		if (currentMethod == null) {
			report_error("Greska: return iskaz se mora naci unutar metode!", returnNoExpr);
			return;
		}
		returnFound = true;
		if (currentMethod.obj.getType().getKind() != Struct.None)
			report_error("Greska: return iskaz (bez izraza) se mora naci iskljucivo unutar metode deklarisane kao void!", returnNoExpr);
	}
	
	public void visit(ReadStmt readStmt) {
		int designatorKind = readStmt.getDesignator().obj.getKind();
		if ((designatorKind != Obj.Var || (designatorKind == Obj.Var && (readStmt.getDesignator().obj.getType().getKind() == Struct.Array || readStmt.getDesignator().obj.getType().getKind() == Struct.Class)))
				&& designatorKind != Obj.Elem && designatorKind != Obj.Fld)
			report_error("Greska: Argument read metode mora biti ili promenljiva ili element niza ili polje klase!", readStmt);
	}
	
	public void visit(MatchedStatement matchedStatement) {
		if (matchedStatement.getCondition().struct != SemanticPass.boolType)
			report_error("Greska: Tip uslova u if naredbi mora biti bool!", matchedStatement);
	}
	
	public void visit(Assignment assignment) {
		if (assignment.getDesignator().obj.getType().compatibleWith(assignment.getExpr().struct) == false
				&& areObjectsAssignable(assignment.getDesignator().obj.getType(), assignment.getExpr().struct) == false) {
			report_error("Greska: Nekompatibilni tipovi prilikom dodele vrednosti!", assignment);
			assignment.struct = Tab.noType;
		}
		else
			assignment.struct = assignment.getDesignator().obj.getType();
	}
	
	public void visit(FunctionCall functionCall) {
		Obj funcObj = functionCall.getDesignator().obj;
		if (funcObj.getKind() != Obj.Meth) {
			report_error("Greska: Ne postoji funkcija " + funcObj.getName() + "!", functionCall);
			functionCall.struct = Tab.noType;
			return;
		}
		if (checkActualParams(functionCall.getLine()) == false)
			functionCall.struct = Tab.noType;
		else
			functionCall.struct = funcObj.getType();
		functionFormalParams.pop();
		functionActualParams.pop();
	}
	
	public void visit(Increment increment) {
		if (increment.getDesignator().obj.getType() != Tab.intType)
			report_error("Greska: Operand inkrement operatora mora biti tipa int!", increment);
	}
	
	public void visit(Decrement decrement) {
		if (decrement.getDesignator().obj.getType() != Tab.intType)
			report_error("Greska: Operand dekrement operatora mora biti tipa int!", decrement);
	}
	
	public void visit(DoNonTerminal doNonTerminal) {
		insideDoWhileLoop++;
	}

	public void visit(SwitchNonTerminal switchNonTerminal) {
		caseSets.push(new HashSet<>());
	}
	
	public void visit(EmptyCaseStmt emptyCaseStmt) {
		if (caseSets.peek().contains(emptyCaseStmt.getNUMCONSTNonTerminal().getN1()) == true)
			report_error("Greska: Vise case grana sa istim brojem!", emptyCaseStmt);
		else
			caseSets.peek().add(emptyCaseStmt.getNUMCONSTNonTerminal().getN1());
	}
	
	public void visit(CaseStmt caseStmt) {
		if (caseSets.peek().contains(caseStmt.getNUMCONSTNonTerminal().getN1()) == true)
			report_error("Greska: Vise case grana sa istim brojem!", caseStmt);
		else
			caseSets.peek().add(caseStmt.getNUMCONSTNonTerminal().getN1());
	}
	
	public void visit(CasesStmt casesStmt) {
		if (caseSets.peek().contains(casesStmt.getNUMCONSTNonTerminal().getN1()) == true)
			report_error("Greska: Vise case grana sa istim brojem!", casesStmt);
		else
			caseSets.peek().add(casesStmt.getNUMCONSTNonTerminal().getN1());
	}
	
	public void visit(CasesEmptyStmt casesEmptyStmt) {
		if (caseSets.peek().contains(casesEmptyStmt.getNUMCONSTNonTerminal().getN1()) == true)
			report_error("Greska: Vise case grana sa istim brojem!", casesEmptyStmt);
		else
			caseSets.peek().add(casesEmptyStmt.getNUMCONSTNonTerminal().getN1());
	}
	
	public void visit(ConditionalTerm conditionalTerm) {
		conditionalTerm.struct = conditionalTerm.getCondTerm().struct;
	}
	
	public void visit(ConditionalTerms conditionalTerms) {
		conditionalTerms.struct = SemanticPass.boolType;
	}
	
	public void visit(ConditionalFact conditionalFact) {
		conditionalFact.struct = conditionalFact.getCondFact().struct;
	}
	
	public void visit(ConditionalFacts conditionalFacts) {
		conditionalFacts.struct = SemanticPass.boolType;
	}
	
	public void visit(CondExpr condExpr) {
		condExpr.struct = condExpr.getExpr().struct;
	}
	
	public void visit(CondRel condRel) {
		Struct expr1Struct = condRel.getExpr1().struct;
		Struct expr2Struct = condRel.getExpr11().struct;
		if (expr1Struct.compatibleWith(expr2Struct) == false) {
			report_error("Greska: Nekompatibilni tipovi u relacionom izrazu!", condRel);
			condRel.struct = Tab.noType;
		}
		else
			condRel.struct = SemanticPass.boolType;
			
	}
	
	public void visit(Expression expression) {
		expression.struct = expression.getExpr1().struct;
	}
	
	public void visit(ConditionalExpression conditionalExpression) {
		Struct expr1Struct = conditionalExpression.getExpr1().struct;
		Struct expr2Struct = conditionalExpression.getExpr11().struct;
		if (expr1Struct.equals(expr2Struct) == false) {
			report_error("Greska: Drugi i treci tip u ternarnom izrazu nisu isti!", conditionalExpression);
			conditionalExpression.struct = Tab.noType;
		}
		else
			conditionalExpression.struct = expr1Struct; // Or expr2Struct
	}
	
	public void visit(NormalExpr normalExpr) {
		normalExpr.struct = normalExpr.getNormExpr().struct;
	}
	
	public void visit(NegatedExpr negatedExpr) {
		if (negatedExpr.getNegExpr().struct != Tab.intType) {
			report_error("Greska: Izraz posle znaka '-' mora biti tipa int!", negatedExpr);
			negatedExpr.struct = Tab.noType;
		}
		else
			negatedExpr.struct = negatedExpr.getNegExpr().struct;
	}
	
	public void visit(AddExpr addExpr) {
		Struct termStruct = addExpr.getTerm().struct;
		Struct exprStruct = addExpr.getNormExpr().struct;
		if (termStruct.equals(exprStruct) == true && termStruct == Tab.intType)
			addExpr.struct = exprStruct;
		else {
			report_error("Greska: Nekompatibilni tipovi u izrazu za sabiranje!", addExpr);
			addExpr.struct = Tab.noType;
		}
	}
	
	public void visit(TermExpr termExpr) {
		termExpr.struct = termExpr.getTerm().struct;
	}
	
	public void visit(NegExpression negExpression) {
		negExpression.struct = negExpression.getNormExpr().struct;
	}
	
	public void visit(BasicTerm basicTerm) {
		basicTerm.struct = basicTerm.getFactor().struct;
	}
	
	public void visit(MulTerm mulTerm) {
		Struct termStruct = mulTerm.getTerm().struct;
		Struct factorStruct = mulTerm.getFactor().struct;
		if (termStruct.equals(factorStruct) == true && termStruct == Tab.intType)
			mulTerm.struct = factorStruct;
		else {
			report_error("Greska: Tipovi oba operanda u izrazu za mnozenje moraju biti int!", mulTerm);
			mulTerm.struct = Tab.noType;
		}
	}
	
	public void visit(NumberConst numberConst) {
		numberConst.struct = Tab.intType;
	}
	
	public void visit(CharacterConst characterConst) {
		characterConst.struct = Tab.charType;
	}
	
	public void visit(BooleanConst booleanConst) {
		booleanConst.struct = SemanticPass.boolType;
	}
	
	public void visit(Var var) {
		var.struct = var.getDesignator().obj.getType();
	}
	
	public void visit(FuncCall funcCall) {
		Obj funcObj = funcCall.getDesignator().obj;
		if (funcObj.getKind() != Obj.Meth) {
			report_error("Greska: Ne postoji funkcija " + funcObj.getName() + "!", funcCall);
			funcCall.struct = Tab.noType;
			return;
		}
		if (checkActualParams(funcCall.getLine()) == false)
			funcCall.struct = Tab.noType;
		else
			funcCall.struct = funcObj.getType();
		functionFormalParams.pop();
		functionActualParams.pop();
	}
	// Actual and formal parameters: the number of both must be the same, as well as the type of pair (actual_parameter, formal_parameter)
	private boolean checkActualParams(int line) {
		if (functionActualParams.peek().size() != functionFormalParams.peek().size()) {
			report_error("Greska: Broj stvarnih i formalnih parametara nije isti na liniji " + line, null);
			return false;
		}
		for (int i = 0; i < functionActualParams.peek().size(); i++)
			if (functionActualParams.peek().get(i).struct.compatibleWith(
					functionFormalParams.peek().get(i).getType()) == false &&
					areObjectsAssignable(functionActualParams.peek().get(i).struct, functionFormalParams.peek().get(i).getType())) {
				report_error("Greska: Stvarni i formalni parametar broj " + (i + 1) + " nisu kompatibilni na liniji " + line, null);
				return false;
			}		
		return true;
	}
	
	public void visit(VarAlloc varAlloc) {
		if (currentType.struct.getKind() != Struct.Class) {
			report_error("Greska: Tip dinamicki alocirane promenljive mora biti unutrasnja klasa!", varAlloc);
			varAlloc.struct = Tab.noType;
		}
		else
			varAlloc.struct = currentType.struct;
	}
	
	public void visit(ArrayAlloc arrayAlloc) {
		if (arrayAlloc.getExpr().struct != Tab.intType) {
			report_error("Greska: Izraz koji oznacava zeljenu velicinu dinamicki alociranog niza nije tipa int!", arrayAlloc);
			arrayAlloc.struct = Tab.noType;
		}
		else
			arrayAlloc.struct = new Struct(Struct.Array, currentType.struct);
	}
	
	public void visit(ParenFactor parenFactor) {
		parenFactor.struct = parenFactor.getExpr().struct;
	}
	
	public void visit(ActualParam actualParam) {
		functionActualParams.peek().add(actualParam.getExpr());
	}
	
	public void visit(ActualParams actualParams) {
		functionActualParams.peek().add(actualParams.getExpr());
	}
	
	public void visit(DesignatorIdent designatorIdent) {
		Obj obj = Tab.find(designatorIdent.getName());
		if (obj == Tab.noObj) {
			report_error("Greska: Ime " + designatorIdent.getName() + " nije deklarisano!", designatorIdent);
			designatorIdent.obj = Tab.noObj;
			return;
		}
		designatorIdent.obj = obj;
		if (obj.getKind() == Obj.Meth) {
			functionActualParams.push(new ArrayList<>());
			functionFormalParams.push(new ArrayList<>());
			fillFunctionParams(designatorIdent.obj);
		}
	}
	
	private void fillFunctionParams(Obj functionObj) {
		for (Obj obj : functionObj.getLocalSymbols()) {
			if (obj.getFpPos() == 0) continue; // If fpPos == 0, obj is either parameter this or a local variable
			functionFormalParams.peek().add(obj);
		}
	}
	
	public void visit(DesignatorAttribute designatorAttribute) {
		String name = getDesignatorName(designatorAttribute.getDesignator());
		Obj obj = null;
		if (designatorAttribute.getDesignator().obj.getKind() == Obj.Fld) {
			obj = ((DesignatorAttribute) designatorAttribute.getDesignator()).getDesignator().obj.getType().getMembersTable().searchKey(name);
			if (obj == null) {
				designatorAttribute.obj = Tab.noObj;
				return;
			}
		}
		else
			obj = Tab.find(name);
		
		if (obj == Tab.noObj) {
			designatorAttribute.obj = Tab.noObj;
			return;
		}
		
		if (obj.getType().getKind() != Struct.Class &&
				(obj.getType().getKind() == Struct.Array && obj.getType().getElemType().getKind() != Struct.Class)) {
			report_error("Greska: Ime " + name + " nije objekat!", designatorAttribute);
			return;
		}
		Obj attributeObj = null;
		if (obj.getName().equals("this")) // Current class attributes and methods are not yet chained into the memebers table
			attributeObj = currentClassObjs.searchKey(designatorAttribute.getAttributeName());
		else {
			if (obj.getType().getKind() == Struct.Class)
				attributeObj = obj.getType().getMembersTable().searchKey(designatorAttribute.getAttributeName());
			else if (obj.getType().getKind() == Struct.Array)
				attributeObj = obj.getType().getElemType().getMembersTable().searchKey(designatorAttribute.getAttributeName());
		}
		if (attributeObj == null) {
			report_error("Greska: Klasa objekta " + obj.getName() + " ne sadrzi atribut " + designatorAttribute.getAttributeName(), designatorAttribute);
			designatorAttribute.obj = Tab.noObj;
			return;
		}
		designatorAttribute.obj = attributeObj;
		if (attributeObj.getKind() == Obj.Meth) {
			functionActualParams.push(new ArrayList<>());
			functionFormalParams.push(new ArrayList<>());
			fillFunctionParams(designatorAttribute.obj);
		}
	}
	
	private String getDesignatorName(Designator designator) {
		if (designator instanceof DesignatorIdent)
			return ((DesignatorIdent) designator).getName();
		else if (designator instanceof DesignatorAttribute)
			return ((DesignatorAttribute) designator).getAttributeName();
		else if (designator instanceof DesignatorElement)
			return getDesignatorName(((DesignatorElement) designator).getDesignator());
		return null; // Unreachable code: Designator must be instanceof either DesignatorIdent, DesignatorAttribute or DesignatorElement
	}
	
	public void visit(DesignatorElement designatorElement) {
		String name = getDesignatorName(designatorElement.getDesignator());
		Obj obj = designatorElement.getDesignator().obj;
		if (obj == Tab.noObj) {
			designatorElement.obj = Tab.noObj;
			return; // Semantic pass should never get to this point - to be implemented!
		}
		if (obj.getType().getKind() != Struct.Array) {
			report_error("Greska: Ime " + name + " nije niz!", designatorElement);
			designatorElement.obj = Tab.noObj;
			return;
		}
		if (designatorElement.getExpr().struct != Tab.intType) {
			report_error("Greska: Izraz za indeksiranje niza nije tipa int!", designatorElement);
			designatorElement.obj = Tab.noObj;
			return;
		}
		designatorElement.obj = new Obj(Obj.Elem, name, obj.getType().getElemType());
	}
	
}
