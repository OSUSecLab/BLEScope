package edu.utdallas.s3.vsa.backwardslicing;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Stack;

import org.javatuples.Pair;
import org.json.JSONObject;

import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AbstractStmtSwitch;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.LengthExpr;
import soot.jimple.NewArrayExpr;
import soot.jimple.NullConstant;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JimpleLocal;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.CompleteBlockGraph;
import edu.utdallas.s3.vsa.base.GlobalStatistics;
import edu.utdallas.s3.vsa.base.ParameterTransferStmt;
import edu.utdallas.s3.vsa.base.StmtPoint;
import edu.utdallas.s3.vsa.base.TargetType;
import edu.utdallas.s3.vsa.forwardexec.StmtPath;
import edu.utdallas.s3.vsa.graph.DGraph;
import edu.utdallas.s3.vsa.graph.HeapObject;
import edu.utdallas.s3.vsa.graph.ValuePoint;
import edu.utdallas.s3.vsa.main.Config;
import edu.utdallas.s3.vsa.utility.BlockGenerator;
import edu.utdallas.s3.vsa.utility.Logger;
import edu.utdallas.s3.vsa.utility.OtherUtility;

public class BackwardContext extends AbstractStmtSwitch implements StmtPath, ICollecter {

	ValuePoint startPoint;
	DGraph dg;

	ArrayList<SootMethod> methodes;
	ArrayList<Pair<Block, Integer>> blockes;
	Unit currentInstruction;

	HashSet<Value> intrestedVariable;
	ArrayList<StmtPoint> execTrace;

	HashSet<HeapObject> dependentHeapObjects;
	Stack<CallStackItem> callStack;

	// HashSet<DataSourceType> dataSrcs;

	boolean finished = false;

	@SuppressWarnings("unchecked")
	public BackwardContext(BackwardContext oldBc) {
		startPoint = oldBc.getStartPoint();
		dg = oldBc.getDg();
		methodes = (ArrayList<SootMethod>) oldBc.getMethodes().clone();
		blockes = (ArrayList<Pair<Block, Integer>>) oldBc.getBlockes().clone();
		currentInstruction = oldBc.getCurrentInstruction();
		intrestedVariable = (HashSet<Value>) oldBc.getIntrestedVariable().clone();
		execTrace = (ArrayList<StmtPoint>) oldBc.getExecTrace().clone();
		dependentHeapObjects = (HashSet<HeapObject>) oldBc.getDependentHeapObjects().clone();
		callStack = (Stack<CallStackItem>) oldBc.getCallStack().clone();
		// dataSrcs = (HashSet<DataSourceType>) oldBc.getDataSrcs().clone();
	}

	public BackwardContext(ValuePoint startPoint, DGraph dg) {
		this.startPoint = startPoint;
		this.dg = dg;

		intrestedVariable = new HashSet<Value>();
		execTrace = new ArrayList<StmtPoint>();
		dependentHeapObjects = new HashSet<HeapObject>();
		callStack = new Stack<CallStackItem>();

		methodes = new ArrayList<SootMethod>();
		methodes.add(0, startPoint.getMethod_location());

		blockes = new ArrayList<Pair<Block, Integer>>();
		setCurrentBlock(startPoint.getBlock_location());

		// dataSrcs = new HashSet<DataSourceType>();

		currentInstruction = startPoint.getInstruction_location();

		execTrace.add(0, new StmtPoint(startPoint.getMethod_location(), startPoint.getBlock_location(), startPoint.getInstruction_location()));

		// init
		Value tmp;
		for (int index : startPoint.getTargetRgsIndexes()) {
			if (index == TargetType.RIGHTPART.getType()) {// set heap object
				tmp = ((JAssignStmt) currentInstruction).getRightOp();
			} else if (index == TargetType.BASEOBJECT.getType()) {
				tmp = ((soot.jimple.InstanceInvokeExpr) ((Stmt) currentInstruction).getInvokeExpr()).getBase();
			} else {
				tmp = ((Stmt) currentInstruction).getInvokeExpr().getArg(index);
			}

			if (tmp instanceof JimpleLocal) {
				Logger.printI("Target Variable is" + tmp.getClass() + " " + currentInstruction);
				this.addIntrestedVariableIfNotConstant(tmp);
			} else if (OtherUtility.isStrConstant(tmp)) {
				// this.addNewDataSrc(DataSourceType.HARDCODED_STR);
			} else if (OtherUtility.isNumConstant(tmp)) {
				// this.addNewDataSrc(DataSourceType.HARDCODED_NUM);
			} else if (tmp instanceof NullConstant) {
				Logger.printI("Target Variable is null " + currentInstruction);
			} else {
				Logger.printW("Target Variable is" + tmp.getClass() + " " + currentInstruction);
			}
		}
	}

	public void finished() {
		finished = true;
	}

	public boolean backWardHasFinished() {
		// return intrestedVariable.size() == 0;
		return finished || intrestedVariable.size() == 0 || this.getMethodes().size() > Config.MAXMETHODCHAINLEN;
	}

	public List<BackwardContext> oneStepBackWard() {

		Unit nextInstrct = this.getCurrentBlock().getPredOf(currentInstruction);
		// Logger.print(this.hashCode() + "oneStepBackWard");
		if (nextInstrct != null) {
			return oneStepBackWard(nextInstrct);
		} else {
			List<BackwardContext> newBc = new ArrayList<BackwardContext>();
			BackwardContext tmp;
			// Logger.print(this.hashCode() +
			// this.getCurrentMethod().toString());
			// Logger.print(this.hashCode() +
			// this.getCurrentMethod().retrieveActiveBody().toString());
			// Logger.print(this.hashCode() +
			// this.getCurrentBlock().toString());
			CompleteBlockGraph cbg = BlockGenerator.getInstance().generate(this.getCurrentMethod().retrieveActiveBody());
			if (cbg.getHeads().contains(this.getCurrentBlock())) {
				// go back to other method
				GlobalStatistics.getInstance().countBackWard2Caller();
				if (this.getCallStack().isEmpty()) {
					// Logger.print("111111");
					boolean allisParameterRef = true;
					String ostr = "";
					for (Value var : this.getIntrestedVariable()) {
						ostr += var + ",";
						if (!(var instanceof ParameterRef)) {
							allisParameterRef = false;
						}
					}
					if (!allisParameterRef) {
						Logger.printW(String.format("[%s] [Not all the intresteds are ParameterRef]: %s", this.hashCode(), ostr));
						finished = true;
						return newBc;
					}

					return oneStepBackWard2Caller();
				} else {// back call
					// Logger.print("22222");
					getBackFromACall();
					return newBc;
				}
			} else {
				// go back to previous block
				// Logger.print("33333");

				List<Block> bs = BlockGenerator.removeBlocksThatHaveBeenVisitedTwice(this.getBlockes(), cbg.getPredsOf(this.getCurrentBlock()));

				// else {
				// if (!BlockGenerator.isCircle(block, this.getCurrentBlock(),
				// cbg))
				// bs.add(block);
				// }
				// }

				/*
				 * List<Block> bs = new ArrayList<Block>();
				 * bs.addAll(cbg.getPredsOf(this.getCurrentBlock()));
				 * BlockGenerator.removeCircleBlocks(bs, this.getCurrentBlock(),
				 * cbg);
				 */

				// !!!!!!!!!!!!!!!!May 5th, needs look up
				// com.kinsahealth.ble_sdk.manager.devices.ble_platform.protocol.KCICommand.getPayload()

				if (bs.size() == 0) {
					Logger.printW(String.format("[%s] [No PredsOf]: %s", this.hashCode(), this.getCurrentInstruction()));
					finished = true;
					return newBc;
				}

				this.setCurrentBlock(bs.get(0));

				for (Block tb : bs) {
					if (tb == this.getCurrentBlock())
						continue;

					tmp = this.clone();
					tmp.setCurrentBlock(tb);
					newBc.addAll(tmp.oneStepBackWard(tb.getTail()));
					newBc.add(tmp);
				}

				newBc.addAll(this.oneStepBackWard(this.getCurrentBlock().getTail()));
				return newBc;
			}
		}
	}

	public List<BackwardContext> oneStepBackWard(Unit nextInstrct) {
		List<BackwardContext> newBc = new ArrayList<BackwardContext>();
		currentInstruction = nextInstrct;

		boolean containsIntrestedThings = false;
		for (ValueBox box : currentInstruction.getUseAndDefBoxes()) {
			if (intrestedVariable.contains(box.getValue())) {
				containsIntrestedThings = true;
				break;
			} else if (box.getValue() instanceof ArrayRef && intrestedVariable.contains(((ArrayRef) box.getValue()).getBase())) {
				containsIntrestedThings = true;
				break;
			}
		}
		String ostr = this.getIntrestedVariableString();
		Logger.printI(String.format("[%s] [Next Ins]: %s (%s)", this.hashCode(), currentInstruction, containsIntrestedThings ? "Y" : "N"));

		if (!containsIntrestedThings) {
			return newBc;
		}

		// Stmt stmt = (Stmt) currentInstruction;
		StmtPoint stmt = new StmtPoint(this.getCurrentMethod(), this.getCurrentBlock(), currentInstruction);
		this.getExecTrace().add(0, stmt);

		this.clear();
		((Stmt) stmt.getInstruction_location()).apply(this);
		newBc.addAll(this.retrieve());
		this.clear();

		String nstr = this.getIntrestedVariableString();
		Logger.printI(String.format("                 %s -> %s ", ostr, nstr));

		return newBc;
	}

	public List<BackwardContext> oneStepBackWard2Caller() {
		List<BackwardContext> newBc = new ArrayList<BackwardContext>();
		List<StmtPoint> sps = StmtPoint.findCaller(this.getCurrentMethod().toString());

		if (sps.size() <= 0) {
			Logger.printW(String.format("[%s] [No Caller]: %s ", this.hashCode(), this.getCurrentMethod().toString()));
			// this.addNewDataSrc(DataSourceType.NOCALLER);
			finished = true;
			return newBc;
		}

		int len = sps.size();
		for (int i = 1; i < len; i++) {
			newBc.add(0, this.clone());
		}
		newBc.add(0, this);

		BackwardContext tmpBC;
		StmtPoint tmpSP;
		for (int i = 0; i < len; i++) {
			tmpBC = newBc.get(i);
			tmpSP = sps.get(i);

			tmpBC.oneStepBackWard2Caller(tmpSP);
		}
		newBc.remove(0);

		return newBc;
	}

	public void oneStepBackWard2Caller(StmtPoint tmpSP) {

		this.setCurrentMethod(tmpSP.getMethod_location());
		this.setCurrentBlock(tmpSP.getBlock_location());
		this.setCurrentInstruction(tmpSP.getInstruction_location());

		String ostr = this.getIntrestedVariableString();
		Logger.printI(String.format("[%s] [Next Ins]: %s (caller:%s)", this.hashCode(), this.getCurrentInstruction(), this.getCurrentMethod()));

		HashMap<Integer, Value> regs = new HashMap<Integer, Value>();
		for (Value var : this.getIntrestedVariable()) {
			regs.put(((ParameterRef) var).getIndex(), var);
		}
		this.getIntrestedVariable().clear();

		InvokeExpr inve = ((Stmt) tmpSP.getInstruction_location()).getInvokeExpr();
		ParameterTransferStmt tmp;
		for (int j : regs.keySet()) {
			this.addIntrestedVariableIfNotConstant(inve.getArg(j));

			tmp = new ParameterTransferStmt(regs.get(j), inve.getArg(j));
			StmtPoint tmpSPaaa = new StmtPoint(this.getCurrentMethod(), this.getCurrentBlock(), tmp);
			this.getExecTrace().add(0, tmpSPaaa);
		}

		String nstr = this.getIntrestedVariableString();
		Logger.printI(String.format("                 %s -> %s ", ostr, nstr));
	}

	public void getBackFromACall() {
		CallStackItem citem = this.getCallStack().pop();

		Stmt retStmt = (Stmt) citem.getCurrentInstruction();

		Value opsite;
		for (Value param : this.getCurrentMethod().getActiveBody().getParameterRefs()) {
			if (this.getIntrestedVariable().contains(param)) {

				opsite = retStmt.getInvokeExpr().getArg(((ParameterRef) param).getIndex());

				this.removeIntrestedVariable(param);
				this.addIntrestedVariableIfNotConstant(opsite);
				StmtPoint tmpSPaaa = new StmtPoint(this.getCurrentMethod(), this.getCurrentBlock(), new ParameterTransferStmt(param, opsite));
				this.getExecTrace().add(0, tmpSPaaa);
			}
		}

		this.setCurrentMethod(citem.getSmethd());
		// Logger.print(this.hashCode() + "back to " + citem.getSmethd());
		this.setCurrentBlock(citem.getBlcok());
		this.setCurrentInstruction(citem.getCurrentInstruction());

	}

	public ValuePoint getStartPoint() {
		return startPoint;
	}

	public void setStartPoint(ValuePoint startPoint) {
		this.startPoint = startPoint;
	}

	public DGraph getDg() {
		return dg;
	}

	public void setDg(DGraph dg) {
		this.dg = dg;
	}

	public SootMethod getCurrentMethod() {
		return getMethodes().get(0);
	}

	public void setCurrentMethod(SootMethod currentMethod) {
		this.getMethodes().add(0, currentMethod);
	}

	public Block getCurrentBlock() {
		return getBlockes().get(0).getValue0();
	}

	public void setCurrentBlock(Block currentBlock) {
		getBlockes().add(0, Pair.with(currentBlock, this.getCallStack().size()));
	}

	public ArrayList<SootMethod> getMethodes() {
		return methodes;
	}

	public ArrayList<Pair<Block, Integer>> getBlockes() {
		return blockes;
	}

	public Unit getCurrentInstruction() {
		return currentInstruction;
	}

	public void setCurrentInstruction(Unit currentInstruction) {
		this.currentInstruction = currentInstruction;
	}

	public String getIntrestedVariableString() {
		String ostr = "";
		for (Value var : this.getIntrestedVariable()) {
			ostr += var + ",";
		}
		return ostr;
	}

	public HashSet<Value> getIntrestedVariable() {
		return intrestedVariable;
	}

	public void addIntrestedVariableIfNotConstant(Value v) {
		if (v instanceof Local) {
			intrestedVariable.add(v);
		} else if (OtherUtility.isStrConstant(v)) {
			// this.addNewDataSrc(DataSourceType.HARDCODED_STR);
		} else if (OtherUtility.isNumConstant(v)) {
			// this.addNewDataSrc(DataSourceType.HARDCODED_NUM);
		} else if (v instanceof NullConstant) {
			Logger.printI("Variable is null no need to taint ");
		} else {
			Logger.printW(String.format("[%s] [unknow addIntrestedVariableIfNotConstant] %s(%s)", this.hashCode(), v, v.getClass()));
		}
	}

	public void addIntrestedVariable(Value v) {
		intrestedVariable.add(v);
	}

	public void removeIntrestedVariable(Value v) {
		intrestedVariable.remove(v);
	}

	public void setIntrestedVariable(HashSet<Value> intrestedVariable) {
		this.intrestedVariable = intrestedVariable;
	}

	public ArrayList<StmtPoint> getExecTrace() {
		return execTrace;
	}

	public ArrayList<StmtPoint> removeFromExecTrace(Unit u) {
		StmtPoint tmp = null;
		for (StmtPoint sp : getExecTrace()) {
			if (sp.getInstruction_location() == u) {
				tmp = sp;
			}
		}
		if (tmp != null)
			getExecTrace().remove(tmp);
		return execTrace;
	}

	// public HashSet<DataSourceType> getDataSrcs() {
	// return dataSrcs;
	// }

	// public void addNewDataSrc(DataSourceType dst) {
	// dataSrcs.add(dst);
	// }

	public void setExecTrace(ArrayList<StmtPoint> execTrace) {
		this.execTrace = execTrace;
	}

	public void printExceTrace() {
		Logger.print("[Start]:" + this.getStartPoint().getInstruction_location());
		for (StmtPoint var : this.getExecTrace()) {
			Logger.print("        " + var.getInstruction_location());// + "  " +
																		// var.getInstruction_location().getClass());
			// if(var.getInstruction_location() instanceof
			// ParameterTransferStmt){
			// Logger.print("                "
			// +((ParameterTransferStmt)var.getInstruction_location()).getRightOp().getClass());
			// }
		}
	}

	public void setDependentHeapObjects(HashSet<HeapObject> dependentHeapObjects) {
		this.dependentHeapObjects = dependentHeapObjects;

	}

	public HashSet<HeapObject> getDependentHeapObjects() {
		return dependentHeapObjects;
	}

	public Stack<CallStackItem> getCallStack() {
		return callStack;
	}

	public BackwardContext clone() {
		BackwardContext tmp = new BackwardContext(this);
		return tmp;
	}

	// //////////////////////////////////////////////////////
	// ////////////////////// StmtSwitch/////////////////////

	@Override
	public void caseAssignStmt(AssignStmt stmt) {
		// TODO Auto-generated method stub
		// Logger.printW("[caseAssignStmt]");
		boolean leftisIntrested = this.getIntrestedVariable().contains(stmt.getLeftOp());
		this.removeIntrestedVariable(stmt.getLeftOp());
		/*
		 * may have bug?
		 */
		Value value = stmt.getRightOp();
		if (value instanceof InvokeExpr) {
			InvokeExpr tmp = (InvokeExpr) value;
			handleInvokeExpr(stmt.getLeftOp(), leftisIntrested, tmp);

		} else if (value instanceof JNewExpr) {
			JNewExpr tjne = (JNewExpr) value;
			String clasName = tjne.getBaseType().toString();
			if (clasName.equals("java.lang.StringBuilder")) {

			} else {
				Logger.printW(String.format("[%s] [Can't Handle caseAssignStmt->JNewExpr]: %s (%s)", this.hashCode(), stmt, value.getClass()));
				// Logger.printW(this.getCurrentMethod().toString());
				// Logger.printW(this.getCurrentBlock().toString());

			}

		} else if (value instanceof NewArrayExpr) {
			NewArrayExpr arraye = (NewArrayExpr) value;
			if (arraye.getBaseType().toString().equals("java.lang.Object")) {

			} else if (arraye.getBaseType().toString().equals("byte")) {

			} else {
				Logger.printW(String.format("[%s] [Can't Handle caseAssignStmt->NewArrayExpr]: %s (%s)(%s)", this.hashCode(), stmt, value.getClass(), arraye.getBaseType()));
			}

		} else if (value instanceof FieldRef) {// dependent
			// Logger.print(((FieldRef) value).toString());
			// Logger.print(((FieldRef) value).getField().toString());
			// Logger.print(((FieldRef)
			// value).getField().getClass().toString());

			HeapObject ho = HeapObject.getInstance(dg, ((FieldRef) value).getField());
			if (!this.getDependentHeapObjects().contains(ho)) {
				this.getDependentHeapObjects().add(ho);
				dg.addNode(ho);
			}

		} else if (value instanceof JimpleLocal) {
			this.addIntrestedVariable(value);
		} else if (value instanceof JArrayRef) {
			this.addIntrestedVariable(((JArrayRef) value).getBase());
			this.addIntrestedVariableIfNotConstant(((JArrayRef) value).getIndex());

		} else if (value instanceof CastExpr) {
			this.addIntrestedVariableIfNotConstant(((CastExpr) value).getOp());
		} else if (OtherUtility.isStrConstant(value)) {
			// this.addNewDataSrc(DataSourceType.HARDCODED_STR);
		} else if (OtherUtility.isNumConstant(value)) {
			// this.addNewDataSrc(DataSourceType.HARDCODED_NUM);
		} else if (value instanceof LengthExpr) {
			Logger.printW(String.format("LengthExpr " + value + " " + ((LengthExpr) value).getOp()));
			this.addIntrestedVariable(((LengthExpr) value).getOp());
		} else if (value instanceof NullConstant) {

		} else if (value instanceof BinopExpr) {
			// + - * /
			BinopExpr be = ((BinopExpr) value);
			this.addIntrestedVariableIfNotConstant(be.getOp1());
			this.addIntrestedVariableIfNotConstant(be.getOp2());

		} else {
			Logger.printW(String.format("[%s] [Can't Handle caseAssignStmt->RightOp]: %s (%s)", this.hashCode(), stmt, value.getClass()));
		}

	}

	@Override
	public void caseInvokeStmt(InvokeStmt stmt) {
		// TODO Auto-generated method stub
		// System.out.println("caseInvokeStmt:" + stmt);
		handleInvokeExpr(null, false, stmt.getInvokeExpr());
		// super.caseInvokeStmt(stmt);
	}

	public void handleInvokeExpr(Value restAssignTo, boolean leftisIntrested, InvokeExpr invokExp) {
		// 11.6_VirtualInvokeExpr->InvokeExpr
		// Logger.printW("[VirtualInvokeExpr]");
		String mthSig = invokExp.getMethod().toString();

		if (mthSig.equals("<java.lang.System: void arraycopy(java.lang.Object,int,java.lang.Object,int,int)>")) {
			if (this.getIntrestedVariable().contains(invokExp.getArg(2))) {

				this.addIntrestedVariableIfNotConstant(invokExp.getArg(0));
			}
		} else if (TaintRules.getInstance().hasRuleFor(mthSig)) {
			// if (leftisIntrested) {
			if (invokExp instanceof InstanceInvokeExpr && TaintRules.getInstance().isBaseIntrested(mthSig))
				this.addIntrestedVariable(((InstanceInvokeExpr) invokExp).getBase());
			for (int i : TaintRules.getInstance().getInterestedArgIndexes(mthSig, invokExp.getArgCount()))
				this.addIntrestedVariableIfNotConstant(invokExp.getArg(i));

			List<Object> sdret = TaintRules.getInstance().getDataSrc(mthSig);
			if (sdret != null) {
			}
			// for (Object obj : sdret) {
			// this.addNewDataSrc(DataSourceType.valueOf(obj.toString()));
			// }
			// }
		} else {
			if (!diveIntoMethodCall(restAssignTo, leftisIntrested, invokExp)) {
				Logger.printW(String.format("[%s] [Can't Handle handleInvokeExpr->handleInvokeExpr]: %s (%s)", this.hashCode(), invokExp, invokExp.getClass()));
				/*
				 * if (invokExp.getMethod().isNative()) {
				 * this.addNewDataSrc(DataSourceType.NATIVE_CALL); for (int i =
				 * 0; i < invokExp.getArgCount(); i++) {
				 * this.addIntrestedVariableIfNotConstant(invokExp.getArg(i)); }
				 * Logger.printW(String.format(
				 * "[%s] [Native call, just add all args]: %s=%s (%s)",
				 * this.hashCode(), restAssignTo, invokExp,
				 * invokExp.getClass()));
				 * 
				 * } else { if (leftisIntrested) {
				 * this.addNewDataSrc(DataSourceType.NO_HANDLED_CALL);
				 * Logger.printW(String.format(
				 * "[%s] [Can't Handle handleInvokeExpr->InvokeExpr]: %s=%s (%s)"
				 * , this.hashCode(), restAssignTo, invokExp,
				 * invokExp.getClass())); if (invokExp instanceof
				 * InstanceInvokeExpr) { // so that we can get all the unhandled
				 * in the logs this.addIntrestedVariable(((InstanceInvokeExpr)
				 * invokExp).getBase()); } }
				 * 
				 * if (invokExp instanceof InstanceInvokeExpr) { // so that we
				 * can get all the unhandled in the logs
				 * this.addIntrestedVariable(((InstanceInvokeExpr)
				 * invokExp).getBase()); } for (int i = 0; i <
				 * invokExp.getArgCount(); i++) {
				 * this.addIntrestedVariableIfNotConstant(invokExp.getArg(i)); }
				 * }
				 */

			}
		}

	}

	@Override
	public void caseIdentityStmt(IdentityStmt stmt) {
		// TODO Auto-generated method stub
		if (this.getIntrestedVariable().contains(stmt.getLeftOp())) {
			this.removeIntrestedVariable(stmt.getLeftOp());
			if (stmt.getRightOp() instanceof ParameterRef) {
				this.addIntrestedVariable(stmt.getRightOp());
			} else {
				Logger.printW(String.format("[%s] [Can't Handle caseIdentityStmt->RightOpUnrecognized]: %s (%s)", this.hashCode(), stmt, stmt.getLeftOp().getClass()));
			}
		} else {
			Logger.printW(String.format("[%s] [Can't Handle caseIdentityStmt->LeftOpNotIntrested]: %s (%s)", this.hashCode(), stmt, stmt.getLeftOp().getClass()));
		}
	}

	@Override
	public void caseIfStmt(IfStmt stmt) {
		// TODO Auto-generated method stub
		Logger.printW("[ignore if]");
	}

	@Override
	public void defaultCase(Object obj) {
		// TODO Auto-generated method stub
		Logger.printW(String.format("[%s] [Can't Handle]: %s (%s)", this.hashCode(), obj, obj.getClass()));
	}

	public boolean diveIntoMethodCall(Value leftOp, boolean leftisIntrested, InvokeExpr ive) {
		GlobalStatistics.getInstance().countDiveIntoMethodCall();
		// Logger.print(this.hashCode() + "diveIntoMethodCall");
		if (!ive.getMethod().getDeclaringClass().isApplicationClass() || !ive.getMethod().isConcrete())
			return false;

		/*
		 * String tm = ive.getMethod().toString(); for (SootMethod sm :
		 * this.getMethodes()) { if (tm.equals(sm.toString()))
		 * Logger.printW(String.format("[%s] [loop call]")); return false; }
		 */

		this.getExecTrace().remove(this.getCurrentInstruction());

		CallStackItem citem = new CallStackItem(this.getCurrentMethod(), this.getCurrentBlock(), this.getCurrentInstruction(), leftOp);
		this.getCallStack().push(citem);
		GlobalStatistics.getInstance().updateMaxCallStack(this.getCallStack().size());

		CompleteBlockGraph cbg = BlockGenerator.getInstance().generate(ive.getMethod().retrieveActiveBody());
		List<Block> tails = new ArrayList<Block>();
		for (Block block : cbg.getTails()) {
			if (leftOp == null || block.getTail() instanceof ReturnStmt) {
				tails.add(block);
			}
		}
		if (tails.size() == 0) {
			Logger.printW(String.format("[%s] [All Tail not ReturnStmt]: %s (%s)", this.hashCode(), this.getCurrentInstruction(), this.getCurrentInstruction().getClass()));
		}

		List<BackwardContext> bcs = new ArrayList<BackwardContext>();
		int len = tails.size();
		// Logger.print(this.hashCode() + "tails.size" + len);

		for (int i = 1; i < len; i++) {
			bcs.add(this.clone());
		}
		bcs.add(0, this);

		BackwardContext tbc;
		Block tblock;
		Stmt rets;
		ParameterTransferStmt tmp;
		for (int i = 0; i < len; i++) {
			tbc = bcs.get(i);
			tblock = tails.get(i);

			rets = (Stmt) tblock.getTail();

			if (leftOp != null && leftisIntrested) {

				if (!(tblock.getTail() instanceof ReturnStmt)) {
					Logger.printW(String.format("[%s] [Tail not ReturnStmt]: %s (%s)", this.hashCode(), tblock.getTail(), tblock.getTail().getClass()));
				}

				tmp = new ParameterTransferStmt(leftOp, ((ReturnStmt) rets).getOp());
				StmtPoint tmpSPaaa = new StmtPoint(this.getCurrentMethod(), this.getCurrentBlock(), tmp);
				tbc.getExecTrace().add(0, tmpSPaaa);

				tbc.addIntrestedVariableIfNotConstant(((ReturnStmt) rets).getOp());// ??
				// parameter
			}

			tbc.setCurrentMethod(ive.getMethod());
			tbc.setCurrentBlock(tblock);
			tbc.setCurrentInstruction(rets);
		}
		bcs.remove(0);

		bcs.forEach(bc -> {
			this.put(bc);
		});
		bcs.clear();

		return true;
	}

	// //////////////////////////////////////////////////////
	// ////////////////////// StmtPath //////////////////////
	@Override
	public Unit getStmtPathHeader() {
		// TODO Auto-generated method stub
		return this.getExecTrace().get(0).getInstruction_location();
	}

	@Override
	public Unit getSuccsinStmtPath(Unit u) {
		// TODO Auto-generated method stub
		if (u == null)
			return null;
		Unit told = null;
		for (StmtPoint tnew : this.getExecTrace()) {
			if (u == told) {
				return tnew.getInstruction_location();
			}
			told = tnew.getInstruction_location();
		}

		return null;
	}

	@Override
	public Unit getPredsinStmtPath(Unit u) {
		// TODO Auto-generated method stub
		if (u == null)
			return null;
		Unit told = null;
		for (StmtPoint tnew : this.getExecTrace()) {
			if (u == tnew.getInstruction_location()) {
				return told;
			}
			told = tnew.getInstruction_location();
		}

		return null;
	}

	@Override
	public Unit getStmtPathTail() {
		// TODO Auto-generated method stub
		return this.getExecTrace().get(this.getExecTrace().size() - 1).getInstruction_location();
	}

	@Override
	public List<StmtPoint> getStmtPath() {
		return this.getExecTrace();
	}

	// //////////////////////////////////////////////////////
	// ////////////////////// ICollecter ////////////////////
	List<BackwardContext> newGeneratedContext = new ArrayList<BackwardContext>();

	@Override
	public void clear() {
		// TODO Auto-generated method stub
		newGeneratedContext.clear();
	}

	@Override
	public void put(BackwardContext bc) {
		newGeneratedContext.add(bc);
	}

	@Override
	public List<BackwardContext> retrieve() {
		// TODO Auto-generated method stub
		return newGeneratedContext;
	}

	// //////////////////////////////////////////////////////

	public JSONObject toJson() {
		JSONObject result = new JSONObject();

		result.put("hashcode", this.hashCode());

		for (SootMethod sm : methodes) {
			result.append("methodes", sm.toString());
		}
		for (Pair<Block, Integer> blk : blockes) {
			result.append("blockes", blk.getValue0().hashCode());
		}
		for (StmtPoint stmt : execTrace) {
			result.append("execTrace", stmt.toJson());
		}

		JSONObject execTraceDetails = new JSONObject();
		HashSet<ValueBox> boxes = new HashSet<ValueBox>();
		for (StmtPoint stmt : execTrace) {
			boxes.addAll(stmt.getInstruction_location().getUseAndDefBoxes());
		}
		JSONObject tmp;
		for (ValueBox vb : boxes) {
			tmp = new JSONObject();
			tmp.put("class", vb.getValue().getClass().getSimpleName());
			tmp.put("str", vb.getValue().toString());
			tmp.put("hashCode", vb.getValue().hashCode() + "");

			execTraceDetails.put(vb.getValue().hashCode() + "", tmp);
		}
		result.put("ValueBoxes", execTraceDetails);

		return result;
	}
}
