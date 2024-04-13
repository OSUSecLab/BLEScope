package edu.utdallas.s3.vsa.graph.specialcase;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

import soot.Body;
import soot.Local;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.CompleteBlockGraph;
import edu.utdallas.s3.vsa.base.StmtPoint;
import edu.utdallas.s3.vsa.graph.DGraph;
import edu.utdallas.s3.vsa.utility.BlockGenerator;

public class FindInClassAdd {

	public static List<StmtPoint> getAll(DGraph dg, SootField sf) {
		// sf.getDeclaringClass().
		List<StmtPoint> sps = new ArrayList<StmtPoint>();
		Body body;
		boolean contains;
		System.out.println(sf.getDeclaringClass());

		for (SootMethod sm : sf.getDeclaringClass().getMethods()) {
			body = sm.retrieveActiveBody();
			contains = false;
			for (ValueBox vb : body.getUseAndDefBoxes()) {

				if (vb.getValue() instanceof FieldRef)
					if (((FieldRef) vb.getValue()).getField().equals(sf)) {
						contains = true;
						break;
					}
			}
			if (contains)
				sps.addAll(onSootMethod(dg, sf, sm));
		}
		return sps;
	}

	private static List<StmtPoint> onSootMethod(DGraph dg, SootField sf, SootMethod sm) {
		List<StmtPoint> sps = new ArrayList<StmtPoint>();

		CompleteBlockGraph cbg = BlockGenerator.getInstance().generate(sm.retrieveActiveBody());
		Local reg = null;
		Unit tu;
		Value tv;
		for (Block block : cbg.getBlocks()) {
			Iterator<Unit> us = block.iterator();
			while (us.hasNext()) {
				tu = us.next();
				if (reg == null) {
					if (tu instanceof AssignStmt) {
						Value vvv = ((AssignStmt) tu).getRightOp();
						if (vvv instanceof FieldRef && ((FieldRef) vvv).getField().equals(sf)) {
							reg = (Local) ((AssignStmt) tu).getLeftOp();
						}
					}
				} else {
					for (ValueBox vb : tu.getUseAndDefBoxes()) {
						tv = vb.getValue();
						if (tv instanceof InstanceInvokeExpr) {

							if (((InstanceInvokeExpr) tv).getBase().equivTo(reg) && tmths.contains(((InstanceInvokeExpr) tv).getMethod().getName())) {
								sps.add(new StmtPoint(sm, block, tu));
							}
						}
					}
				}

			}
		}
		return sps;
	}

	static HashSet<String> tmths = new HashSet<String>();
	static HashSet<String> addableClasses = new HashSet<String>();
	static {
		tmths.add("put");
		tmths.add("add");

		addableClasses.add("java.util.Map");
		addableClasses.add("java.util.HashMap");
		addableClasses.add("java.util.Set");
		addableClasses.add("java.util.HashSet");
	}

	public static boolean isAddable(SootField sf) {
		return addableClasses.contains(sf.getType().toString());
	}

}
/*
 * 
 * public com.telink.bluetooth.light.q a(java.lang.String, java.lang.Object) {
 * com.telink.bluetooth.light.q $r0; java.lang.String $r1; java.lang.Object $r2;
 * java.util.Map $r3;
 * 
 * $r0 := @this: com.telink.bluetooth.light.q;
 * 
 * $r1 := @parameter0: java.lang.String;
 * 
 * $r2 := @parameter1: java.lang.Object;
 * 
 * $r3 = $r0.<com.telink.bluetooth.light.q: java.util.Map a>;
 * 
 * interfaceinvoke $r3.<java.util.Map: java.lang.Object
 * put(java.lang.Object,java.lang.Object)>($r1, $r2);
 * 
 * return $r0; }
 */