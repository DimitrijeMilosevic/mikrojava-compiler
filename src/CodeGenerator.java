package rs.ac.bg.etf.pp1;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import rs.ac.bg.etf.pp1.CounterVisitor.FormParamCounter;
import rs.ac.bg.etf.pp1.CounterVisitor.VarCounter;
import rs.ac.bg.etf.pp1.ast.*;
import rs.etf.pp1.mj.runtime.*;
import rs.etf.pp1.symboltable.Tab;
import rs.etf.pp1.symboltable.concepts.*;

public class CodeGenerator extends VisitorAdaptor {

	public static final int WORD_SIZE_IN_BYTES = 4;
	public static final int WORD_ALLOC_CODE = 1;
	public static final int BYTE_ALLOC_CODE = 0;
	
	private int mainPC; // Stores the address of the main function - starting point of every MJ program
	private Stack<List<Integer>> fixupElseAddresses = new Stack<>();
	private Stack<List<Integer>> fixupExitAddresses = new Stack<>();
	private Stack<Integer> doWhileStartAddresses = new Stack<>();
	private Stack<List<Integer>> fixupExitWhileAddresses = new Stack<>();
	private Stack<List<Integer>> fixupContinueAddresses = new Stack<>();
	private Stack<List<Integer>> fixupExitSwitchAddresses = new Stack<>();
	private Stack<Integer> fixupDropIntoNextCaseAddress = new Stack<>();
	private Stack<Integer> fixupCheckNextCaseAddress = new Stack<>();
	private List<Obj> classObjects = new ArrayList<>();
	private Map<Struct, Integer> classTVFs = new HashMap<>();
	
	public int getMainPC() {
		return mainPC;
	}
	
	/* ProgName */
	public void visit(ProgName progName) {
		// Define functions len, chr and ord
		defineChr();
		defineOrd();
		defineLen();
	}
	
	private void defineChr() {
		Obj obj = Tab.chrObj;
		obj.setAdr(Code.pc);
		
		Code.put(Code.enter);
		// chr takes one argument (an integer) and has no local variables
		Code.put(1);
		Code.put(1);
		Code.put(Code.load_n);
		Code.put(Code.exit);
		Code.put(Code.return_);
	}
	
	private void defineOrd() {
		Obj obj = Tab.ordObj;
		obj.setAdr(Code.pc);
		
		Code.put(Code.enter);
		// ord takes one argument (a character) and has no local variables
		Code.put(1);
		Code.put(1);
		Code.put(Code.load_n);
		Code.put(Code.exit);
		Code.put(Code.return_);
	}
	
	private void defineLen() {
		Obj obj = Tab.lenObj;
		obj.setAdr(Code.pc);
		
		Code.put(Code.enter);
		// len takes one argument (an array) and has no local variables
		Code.put(1);
		Code.put(1);
		Code.put(Code.load_n);
		Code.put(Code.arraylength);
		Code.put(Code.exit);
		Code.put(Code.return_);
	}
	/* ProgName */
	
	/* ClassName */
	public void visit(BaseClassName baseClassName) {
		classObjects.add(baseClassName.obj);
	}
	
	public void visit(DerivedClassName derivedClassName) {
		classObjects.add(derivedClassName.obj);
		if (derivedClassName.obj.getType().getImplementedInterfaces().size() == 1) // Derived class -> Update its inherited methods' addresses
			updateMethodAdrs(derivedClassName.obj.getType().getMembersTable().symbols(),
					derivedClassName.obj.getType().getImplementedInterfaces().iterator().next().getMembersTable().symbols());
	}
	
	private void updateMethodAdrs(Collection<Obj> derivedMembers, Collection<Obj> baseMembers) {
		for (Obj derivedMethod : derivedMembers) {
			if (derivedMethod.getKind() != Obj.Meth) continue;
			for (Obj baseMethod : baseMembers) {
				if (baseMethod.getKind() != Obj.Meth) continue;
				if (baseMethod.getName().equalsIgnoreCase(derivedMethod.getName()) == true) {
					derivedMethod.setAdr(baseMethod.getAdr());
					break;
				}
			}
		}
	}
	/* ClassName */
	
	/* MethodDecl */
	public void visit(MethodDecl methodDecl) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}
	/* MethodDecl */
	
	/* MethodName */
	public void visit(RetMethodName retMethodName) {
		retMethodName.obj.setAdr(Code.pc);
		SyntaxNode methodNode = retMethodName.getParent();
		// Calculate number of local variables and number of parameters - for entry instruction
		VarCounter varCounter = new VarCounter();
		methodNode.traverseTopDown(varCounter);
		FormParamCounter formParamCounter = new FormParamCounter();
		methodNode.traverseTopDown(formParamCounter);
		// Generate the entry
		Code.put(Code.enter);
		if (retMethodName.obj.getLevel() == 0) { // Global function
			Code.put(formParamCounter.getCount());
			Code.put(formParamCounter.getCount() + varCounter.getCount());
		}
		else { // A method -> We have one more parameter - "this"
			Code.put(formParamCounter.getCount() + 1);
			Code.put(formParamCounter.getCount() + varCounter.getCount() + 1);
		}
	}
	
	public void visit(VoidMethodName voidMethodName) {
		if ("main".equalsIgnoreCase(voidMethodName.getMethodName()) == true) {
			mainPC = Code.pc;
			createTVFs();
		}
		voidMethodName.obj.setAdr(Code.pc);
		SyntaxNode methodNode = voidMethodName.getParent();
		// Calculate number of local variables and number of parameters - for entry instruction
		VarCounter varCounter = new VarCounter();
		methodNode.traverseTopDown(varCounter);
		FormParamCounter formParamCounter = new FormParamCounter();
		methodNode.traverseTopDown(formParamCounter);
		// Generate the entry
		Code.put(Code.enter);
		if (voidMethodName.obj.getLevel() == 0) { // Global function
			Code.put(formParamCounter.getCount());
			Code.put(formParamCounter.getCount() + varCounter.getCount());
		}
		else { // A method -> We have one more parameter - "this"
			Code.put(formParamCounter.getCount() + 1);
			Code.put(formParamCounter.getCount() + varCounter.getCount() + 1);
		}
	}
	/* MethodName */
	
	private void createTVFs() {
		int nextIndex = Code.dataSize;
		for (Obj classObject : classObjects) {
			classTVFs.put(classObject.getType(), nextIndex);
			for (Obj localObj : classObject.getType().getMembersTable().symbols()) {
				if (localObj.getKind() != Obj.Meth) continue;
				String methodName = localObj.getName();
				for (int i = 0; i < methodName.length(); i++) {
					Code.loadConst(methodName.charAt(i));
					Code.put(Code.putstatic);
					Code.put2(nextIndex);
					nextIndex++;
					Code.dataSize++;
				}
				Code.put(Code.const_m1);
				Code.put(Code.putstatic);
				Code.put2(nextIndex);
				nextIndex++;
				Code.dataSize++;
				Code.loadConst(localObj.getAdr());
				Code.put(Code.putstatic);
				Code.put2(nextIndex);
				nextIndex++;
				Code.dataSize++;
			}
		}
	}
	
	/* Unmatched */
	public void visit(UnmatchedIf unmatchedIf) {
		// EXIT
		// We need to update the fixupExitAddresses
		for (int fixupExitAddress : fixupExitAddresses.peek())
			Code.fixup(fixupExitAddress);
		fixupExitAddresses.pop();
	}
	
	public void visit(UnmatchedIfElse unmatchedIfElse) {
		// EXIT
		// We need to update the fixupExitAddresses
		for (int fixupExitAddress : fixupExitAddresses.peek())
			Code.fixup(fixupExitAddress);
		fixupElseAddresses.pop();
		fixupExitAddresses.pop();
	}
	/* Unmatched */
	
	/* IfNonTerminal */
	public void visit(IfNonTerminal ifNonTerminal) {
		SyntaxNode parent = ifNonTerminal.getParent();
		fixupExitAddresses.push(new ArrayList<>());
		if (parent.getClass() != UnmatchedIf.class)
			fixupElseAddresses.push(new ArrayList<>());	
	}
	/* IfNonTerminal */
	
	/* RParenNonTerminal */
	public void visit(RParenNonTerminal rParenNonTerminal) {
		/*
			Stack (top to bottom):
				- Condition: 1 or 0
				- ...
		*/
		Code.loadConst(0);
		Code.putFalseJump(Code.ne, 0); // if (Condition != 0)
		if (rParenNonTerminal.getParent().getClass() == UnmatchedIf.class) // No else
			fixupExitAddresses.peek().add(Code.pc - 2);
		else
			fixupElseAddresses.peek().add(Code.pc - 2);
	}
	/* RParenNonTerminal */
	
	/* ElseNonTerminal */
	public void visit(ElseNonTerminal elseNonTerminal) {
		// CodeGenerator generated bytecode for the then branch. Now we need to skip the else branch
		Code.putJump(0);
		fixupExitAddresses.peek().add(Code.pc - 2);
		// ELSE
		// We need to update the fixupElseAddresses!
		for (int fixupElseAddress : fixupElseAddresses.peek())
			Code.fixup(fixupElseAddress);
	}
	/* ElseNonTerminal */
	
	/* Matched */
	public void visit(DoWhileLoop doWhileLoop) {
		// Stack (top to bottom): - Condition: 1 or 0
		Code.loadConst(0);
		Code.putFalseJump(Code.eq, doWhileStartAddresses.peek()); // while (Condition != 0)
		// EXIT -> Update fixupExitWhileAddresses
		for (int fixupExitWhileAddress : fixupExitWhileAddresses.peek())
			Code.fixup(fixupExitWhileAddress);
		fixupExitWhileAddresses.pop();
		doWhileStartAddresses.pop();
	}
	
	public void visit(SwitchStmt switchStmt) {
		// EXIT from switch statement -> Update fixupExitSwitchAddresses
		for (int fixupExitSwitchAddress : fixupExitSwitchAddresses.peek())
			Code.fixup(fixupExitSwitchAddress);
		fixupExitSwitchAddresses.pop();
		// Do the fixup for the last case statement
		Code.fixup(fixupDropIntoNextCaseAddress.peek());
		fixupDropIntoNextCaseAddress.pop();
		Code.fixup(fixupCheckNextCaseAddress.peek());
		fixupCheckNextCaseAddress.pop();
	}
	
	public void visit(BreakStmt breakStmt) {
		// Break statement is either a part of a do while loop or a case
		SyntaxNode parent = breakStmt.getParent();
		while (parent.getClass() != DoWhileLoop.class && parent.getClass() != CaseStmt.class
				&& parent.getClass() != CasesStmt.class)
			parent = parent.getParent();
		Code.putJump(0);
		if (parent.getClass() == DoWhileLoop.class)
			fixupExitWhileAddresses.peek().add(Code.pc - 2);
		else
			fixupExitSwitchAddresses.peek().add(Code.pc - 2);
	}
	
	public void visit(ContinueStmt continueStmt) {
		// Continue can only be found inside of a do while loop
		Code.putJump(0);
		fixupContinueAddresses.peek().add(Code.pc - 2);
	}
	
	public void visit(PrintStmt printStmt) {
		if (printStmt.getExpr().struct == Tab.charType) {
			Code.loadConst(1);
			Code.put(Code.bprint);
		}
		else {
			Code.loadConst(WORD_SIZE_IN_BYTES);
			Code.put(Code.print);
		}
	}
	
	public void visit(MultiplePrintStmts multiplePrintStmts) {
		if (multiplePrintStmts.getExpr().struct == Tab.charType) {
			Code.loadConst(1);
			for (int i = 0; i < multiplePrintStmts.getN2() - 1; i++)
				Code.put(Code.dup2);
			for (int i = 0; i < multiplePrintStmts.getN2(); i++)
				Code.put(Code.bprint);
		}
		else {
			Code.loadConst(WORD_SIZE_IN_BYTES);
			for (int i = 0; i < multiplePrintStmts.getN2() - 1; i++)
				Code.put(Code.dup2);
			for (int i = 0; i < multiplePrintStmts.getN2(); i++)
				Code.put(Code.print);
		}
	}
	
	public void visit(ReturnExpr returnExpr) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}
	
	public void visit(ReturnNoExpr returnNoExpr) {
		Code.put(Code.exit);
		Code.put(Code.return_);
	}
	
	public void visit(ReadStmt readStmt) {
		if (readStmt.getDesignator().obj.getType() == Tab.charType) {
			Code.put(Code.bread);
			Code.store(readStmt.getDesignator().obj);
		}
		else {
			Code.put(Code.read);
			Code.store(readStmt.getDesignator().obj);
		}
	}
	
	public void visit(MatchedStatement matchedStmt) {
		// EXIT
		// We need to update the fixupExitAddresses
		for (int fixupExitAddress : fixupExitAddresses.peek())
			Code.fixup(fixupExitAddress);
		fixupElseAddresses.pop();
		fixupExitAddresses.pop();
	}
	/* Matched */
	
	/* DoNonTerminal */
	public void visit(DoNonTerminal doNonTerminal) {
		doWhileStartAddresses.push(Code.pc);
		fixupExitWhileAddresses.push(new ArrayList<>());
		fixupContinueAddresses.push(new ArrayList<>());
	}
	/* DoNonTerminal */
	
	/* WhileNonTerminal */
	public void visit(WhileNonTerminal whileNonTerminal) {
		for (int fixupContinueAddress : fixupContinueAddresses.peek())
			Code.fixup(fixupContinueAddress);
		fixupContinueAddresses.pop();
	}
	/* WhileNonTerminal */
	
	/* SwitchNonTerminal */
	public void visit(SwitchNonTerminal switchNonTerminal) {
		fixupExitSwitchAddresses.push(new ArrayList<>());
		fixupDropIntoNextCaseAddress.push(-1);
		fixupCheckNextCaseAddress.push(-1);
	}
	/* SwitchNonTerminal */
	
	/* CaseStatement */
	public void visit(EmptyCaseStmt emptyCaseStmt) {
		// End of the case statement -> Drop into the next one / drop out of switch if it's the last case statement
		Code.putJump(0);
		fixupDropIntoNextCaseAddress.pop();
		fixupDropIntoNextCaseAddress.push(Code.pc - 2);
	}
	
	public void visit(CaseStmt caseStmt) {
		// End of the case statement -> Drop into the next one / drop out of switch if it's the last case statement
		Code.putJump(0);
		fixupDropIntoNextCaseAddress.pop();
		fixupDropIntoNextCaseAddress.push(Code.pc - 2);
	}
	
	public void visit(CasesStmt casesStmt) {
		// End of the case statement -> Drop into the next one / drop out of switch if it's the last case statement
		Code.putJump(0);
		fixupDropIntoNextCaseAddress.pop();
		fixupDropIntoNextCaseAddress.push(Code.pc - 2);
	}
	
	public void visit(CasesEmptyStmt casesEmptyStmt) {
		// End of the case statement -> Drop into the next one / drop out of switch if it's the last case statement
		Code.putJump(0);
		fixupDropIntoNextCaseAddress.pop();
		fixupDropIntoNextCaseAddress.push(Code.pc - 2);
	}
	/* CaseStatement */
	
	/* NUMCONSTNonTerminal */
	public void visit(NUMCONSTNonTerminal numConstNonTerminal) {
		// Stack (top to bottom): - Switch's expression
		// Update fixupCheckNextCaseAddress
		if (fixupCheckNextCaseAddress.peek() != -1)
			Code.fixup(fixupCheckNextCaseAddress.peek());
		Code.put(Code.dup);
		Code.loadConst(numConstNonTerminal.getN1());
		/*
			Stack (top to bottom):
				- Switch's expression
				- Switch's epxression
				- NUMCONSTNonTerminal's number
		*/
		Code.putFalseJump(Code.eq, 0);
		fixupCheckNextCaseAddress.pop();
		fixupCheckNextCaseAddress.push(Code.pc - 2);
		// Beginning of the case body
		// Update fixupDropIntoNextCaseAddress
		if (fixupDropIntoNextCaseAddress.peek() != -1)
			Code.fixup(fixupDropIntoNextCaseAddress.peek());
	}
	/* NUMCONSTNonTerminal */
	
	/* DesignatorStatement */
	public void visit(Assignment assignment) {
		Code.store(assignment.getDesignator().obj);
	}
	
	public void visit(FunctionCall functionCall) {
		if (functionCall.getDesignator() instanceof DesignatorAttribute ||
				(functionCall.getDesignator() instanceof DesignatorIdent && functionCall.getDesignator().obj.getLevel() == 1)) {
			// Add the TVF pointer to the stack
			if (functionCall.getDesignator() instanceof DesignatorAttribute)
				functionCall.getDesignator().traverseBottomUp(this); // This will put the object back on stack
			else {
				Obj thisObj = functionCall.getDesignator().obj.getLocalSymbols().iterator().next();
				Code.load(thisObj);
			}
			Code.put(Code.getfield);
			Code.put2(0);
			// Call invokevirtual
			Code.put(Code.invokevirtual);
			String methodName = functionCall.getDesignator().obj.getName();
			for (int i = 0; i < methodName.length(); i++)
				Code.put4(methodName.charAt(i));
			Code.put4(-1);
		}
		else {
			int offset = functionCall.getDesignator().obj.getAdr() - Code.pc;
			Code.put(Code.call);
			Code.put2(offset);
		}
		if (functionCall.getDesignator().obj.getType() != Tab.noType)
			Code.put(Code.pop); // Take off the return value of a non-void method that's not being stored anywhere
	}
	
	public void visit(Increment increment) {
		if (increment.getDesignator() instanceof DesignatorElement) {
			/*
				Stack (top to bottom):
					- Element index
					- Array address
					- ...
			*/
			Code.put(Code.dup2);
			/*
			Stack (top to bottom):
				- Element index
				- Array address
				- Element index
				- Array address
				- ...
			 */
			Code.put(Code.aload); // Increment/decrement operands must be of int type or semantic pass won't go through!
		}
		else if (increment.getDesignator() instanceof DesignatorAttribute) {
			Code.put(Code.dup);
			Code.load(increment.getDesignator().obj);
		}
		Code.loadConst(1);
		Code.put(Code.add);
		Code.store(increment.getDesignator().obj);
	}
	
	public void visit(Decrement decrement) {
		if (decrement.getDesignator() instanceof DesignatorElement) {
			/*
				Stack (top to bottom):
					- Element index
					- Array address
					- ...
			*/
			Code.put(Code.dup2);
			/*
			Stack (top to bottom):
				- Element index
				- Array address
				- Element index
				- Array address
				- ...
			 */
			Code.put(Code.aload); // Increment/decrement operands must be of int type or semantic pass won't go through!
		}
		else if (decrement.getDesignator() instanceof DesignatorAttribute) {
			Code.put(Code.dup);
			Code.load(decrement.getDesignator().obj);
		}
		Code.loadConst(1);
		Code.put(Code.sub);
		Code.store(decrement.getDesignator().obj);
	}
	/* DesignatorStatement */
	
	/* Condition */
	public void visit(ConditionalTerms conditionalTerms) {
		/*
			Stack (top to bottom):
				- CondTerm: 1 or 0
				- Condition: 1 or 0
		*/
		Code.put(Code.pop); // Stack (top to bottom): - Condition: 1 or 0
		Code.loadConst(0);
		Code.putFalseJump(Code.eq, 0); // if (Condition == 0)
		// Stack (top to bottom): - ...
		int fixupElseAddress = Code.pc - 2;
		// THEN: Condition is equal to 0 -> Put CondTerm as the end result
		conditionalTerms.getCondTerm().traverseBottomUp(this); // Stack (top to bottom): - CondTerm: 1 or 0
		Code.putJump(0); 
		int fixupExitAddress = Code.pc - 2;
		// ELSE: Condition is not equal to 0 (equal to 1) -> Put 1 as the end result
		Code.fixup(fixupElseAddress);
		Code.loadConst(1);
		// EXIT
		Code.fixup(fixupExitAddress);
	}
	/* Condition */
	
	/* CondTerm */
	public void visit(ConditionalFacts conditionalFacts) {
		/*
			Stack (top to bottom):
				- CondFact: 1 or 0
				- CondTerm: 1 or 0
		*/
		Code.put(Code.pop); // Stack (top to bottom): - CondTerm: 1 or 0
		Code.loadConst(0);
		Code.putFalseJump(Code.ne, 0); // if (CondTerm != 0)
		// Stack (top to bottom): - ...
		int fixupElseAddress = Code.pc - 2;
		// THEN: CondTerm is not equal to 0 (equal to 1) -> Put CondFact as the end result
		conditionalFacts.getCondFact().traverseBottomUp(this); // Stack (top to bottom): - CondFact: 1 or 0
		Code.putJump(0);
		int fixupExitAddress = Code.pc - 2;
		// ELSE: CondTerm is equal to 0 -> Don't check CondFact, put 0 as the end result
		Code.fixup(fixupElseAddress);
		Code.loadConst(0);
		// EXIT
		Code.fixup(fixupExitAddress);
	}
	/* CondTerm */
	
	/* CondFact */
	public void visit(CondExpr condExpr) {
		Code.loadConst(0);
		Code.putFalseJump(Code.ne, 0);
		int fixupElseAddress = Code.pc - 2;
		// THEN
		Code.loadConst(1);
		Code.putJump(0);
		int fixupExitAddress = Code.pc - 2;
		// ELSE
		Code.fixup(fixupElseAddress);
		Code.loadConst(0);
		// EXIT
		Code.fixup(fixupExitAddress);
	}
	
	public void visit(CondRel condRel) {
		Relop relop = condRel.getRelop();
		if (relop instanceof Equalop)
			Code.putFalseJump(Code.eq, 0);
		else if (relop instanceof Notequalop)
			Code.putFalseJump(Code.ne, 0);
		else if (relop instanceof Grtop)
			Code.putFalseJump(Code.gt, 0);
		else if (relop instanceof Grteqop)
			Code.putFalseJump(Code.ge, 0);
		else if (relop instanceof Lssop)
			Code.putFalseJump(Code.lt, 0);
		else if (relop instanceof Lsseqop)
			Code.putFalseJump(Code.le, 0);
		int fixupElseAddress = Code.pc - 2;
		// THEN
		Code.loadConst(1);
		Code.putJump(0);
		int fixupExitAddress = Code.pc - 2;
		// ELSE
		Code.fixup(fixupElseAddress);
		Code.loadConst(0);
		// EXIT
		Code.fixup(fixupExitAddress);
	}
	/* CondFact */
	
	/* Expr */
	public void visit(ConditionalExpression conditionalExpression) {
		/*
			Stack (top to bottom):
				- exprN
				- exprY
				- cf
				- ...
		*/
		Code.put(Code.pop);
		Code.put(Code.pop);
		// Stack (top to bottom): - cf -...
		Code.loadConst(0);
		Code.putFalseJump(Code.ne, 0);
		int fixupElseAddress = Code.pc - 2;
		// THEN
		conditionalExpression.getExpr1().traverseBottomUp(this); // This will put exprY on the top of the stack
		Code.putJump(0); // Skip else
		int fixupExitAddress = Code.pc - 2;
		// ELSE
		Code.fixup(fixupElseAddress);
		conditionalExpression.getExpr11().traverseBottomUp(this); // This will put exprN on the top of the stack
		// EXIT
		Code.fixup(fixupExitAddress);
	}
	/* Expr */
	
	/* NormExpr */
	public void visit(AddExpr addExpr) {
		Addop addop = addExpr.getAddop();
		if (addop instanceof Addoperation)
			Code.put(Code.add);
		else if (addop instanceof Subop)
			Code.put(Code.sub);
	}
	/* NormExpr */
	
	/* NegExpr */
	public void visit(NegExpression negExpression) {
		Code.put(Code.neg);
	}
	/* NegExpr */
	
	/* Term */
	public void visit(MulTerm mulTerm) {
		Mulop mulop = mulTerm.getMulop();
		if (mulop instanceof Muloperation)
			Code.put(Code.mul);
		else if (mulop instanceof Divop)
			Code.put(Code.div);
		else if (mulop instanceof Modop)
			Code.put(Code.rem);
	}
	/* Term */
	
	/* Factor */
	public void visit(NumberConst numberConst) {
		Obj numberConstObj = new Obj(Obj.Con, "$", numberConst.struct);
		numberConstObj.setLevel(0);
		numberConstObj.setAdr(numberConst.getN1());
		Code.load(numberConstObj);
	}
	
	public void visit(CharacterConst characterConst) {
		Obj characterConstObj = new Obj(Obj.Con, "$", characterConst.struct);
		characterConstObj.setLevel(0);
		characterConstObj.setAdr(characterConst.getC1());
		Code.load(characterConstObj);
	}
	
	public void visit(BooleanConst booleanConst) {
		Obj booleanConstObj = new Obj(Obj.Con, "$", booleanConst.struct);
		booleanConstObj.setLevel(0);
		booleanConstObj.setAdr((booleanConst.getB1().equalsIgnoreCase("true")) ? 1 : 0);
		Code.load(booleanConstObj);
	}
	
	public void visit(FuncCall funcCall) {
		if (funcCall.getDesignator() instanceof DesignatorAttribute ||
				(funcCall.getDesignator() instanceof DesignatorIdent && funcCall.getDesignator().obj.getLevel() == 1)) {
			// Add the TVF pointer to the stack
			if (funcCall.getDesignator() instanceof DesignatorAttribute)
				funcCall.getDesignator().traverseBottomUp(this); // This will put the object back on stack
			else {
				Obj thisObj = funcCall.getDesignator().obj.getLocalSymbols().iterator().next();
				Code.load(thisObj);
			}
			Code.put(Code.getfield);
			Code.put2(0);
			// Call invokevirtual
			Code.put(Code.invokevirtual);
			String methodName = funcCall.getDesignator().obj.getName();
			for (int i = 0; i < methodName.length(); i++)
				Code.put4(methodName.charAt(i));
			Code.put4(-1);
		}
		else {
			int offset = funcCall.getDesignator().obj.getAdr() - Code.pc;
			Code.put(Code.call);
			Code.put2(offset);
		}
	}
	
	public void visit(VarAlloc varAlloc) {
		Code.put(Code.new_);
		switch (varAlloc.getType().struct.getKind()) {
		case Struct.Int:
			Code.put2(WORD_SIZE_IN_BYTES);
			break;
		case Struct.Char:
			Code.put2(WORD_SIZE_IN_BYTES);
			break;
		case Struct.Bool:
			Code.put2(WORD_SIZE_IN_BYTES);
			break;
		case Struct.Class:
			int size = (varAlloc.struct.getNumberOfFields() + 1) * WORD_SIZE_IN_BYTES; // +1 because of the TVF
			Code.put2(size);
			// Initialize the TVF: On the stack we have the address of the newly allocated object
			Code.put(Code.dup);
			Code.loadConst(classTVFs.get(varAlloc.getType().struct));
			Code.put(Code.putfield);
			Code.put2(0);
			break;
		}
	}
	
	public void visit(ArrayAlloc arrayAlloc) {
		Code.put(Code.newarray);
		switch (arrayAlloc.getType().struct.getKind()) {
		case Struct.Int:
			Code.put(WORD_ALLOC_CODE);
			break;
		case Struct.Char:
			Code.put(BYTE_ALLOC_CODE);
			break;
		case Struct.Bool:
			Code.put(WORD_ALLOC_CODE);
			break;
		case Struct.Class:
			Code.put(WORD_ALLOC_CODE);
			break;
		}
	}
	/* Factor */
	
	/* Designator */
	public void visit(DesignatorIdent designatorIdent) {
		SyntaxNode parent = designatorIdent.getParent();
		if ((designatorIdent.obj.getKind() == Obj.Fld && 
				parent.getClass() != DesignatorAttribute.class && parent.getClass() != DesignatorElement.class) || // This means we are accessing a field from a method without using this.<field_name> => Put this on the stack before loading
				(designatorIdent.obj.getKind() == Obj.Meth && designatorIdent.obj.getLevel() != 0 && 
				parent.getClass() != DesignatorAttribute.class && parent.getClass() != DesignatorElement.class)) { // This means we are calling a method of a class from another method (maybe, same) of the same class => Put this as the argument
			SyntaxNode methodDeclNode = parent;
			while (methodDeclNode.getClass() != MethodDecl.class)
				methodDeclNode = methodDeclNode.getParent();
			MethodName methodName = ((MethodDecl) methodDeclNode).getMethodName();
			Code.load(methodName.obj.getLocalSymbols().iterator().next()); // "this" Obj node
		}	
		if (parent.getClass() != Assignment.class && parent.getClass() != FunctionCall.class && parent.getClass() != FuncCall.class
				&& parent.getClass() != ReadStmt.class)
			Code.load(designatorIdent.obj);
	}
	
	public void visit(DesignatorAttribute designatorAttribute) {
		if (designatorAttribute.obj.getKind() == Obj.Meth) return;
		SyntaxNode parent = designatorAttribute.getParent();
			if (parent.getClass() != Assignment.class && parent.getClass() != FunctionCall.class && parent.getClass() != FuncCall.class
					&& parent.getClass() != ReadStmt.class && parent.getClass() != Increment.class && parent.getClass() != Decrement.class)
				Code.load(designatorAttribute.obj);
		// If it's a method, on the stack, we already have the object's address ("this" argument)!
	}
	
	public void visit(DesignatorElement designatorElement) {
		SyntaxNode parent = designatorElement.getParent();
		Code.load(designatorElement.obj);
		if (parent.getClass() == Assignment.class || parent.getClass() == Increment.class || parent.getClass() == Decrement.class
				|| parent.getClass() == ReadStmt.class)
			Code.pc--; // We must not load the element!
	}
	/* Designator */
	
}
