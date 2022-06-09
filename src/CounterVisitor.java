package rs.ac.bg.etf.pp1;

import rs.ac.bg.etf.pp1.ast.*;

public class CounterVisitor extends VisitorAdaptor {

	protected int count;
	
	public int getCount() {
		return count;
	}
	
	public static class FormParamCounter extends CounterVisitor {
	
		public void visit(FormalParamDecls formParamDecls) {
			count++;
		}
		
		public void visit(SingleFormalParamDecl singleFormalParamDecl) {
			count++;
		}
		
	}
	
	public static class VarCounter extends CounterVisitor{
		
		public void visit(VarIdent varIdent){
			count++;
		}
		
		public void visit(ArrIdent arrIdent) {
			count++;
		}
		
	}
}
