package edu.utdallas.s3.vsa.forwardexec;

import java.util.List;

import soot.Unit;
import edu.utdallas.s3.vsa.base.StmtPoint;

public interface StmtPath {

	public Unit getStmtPathHeader();

	public Unit getSuccsinStmtPath(Unit u);

	public Unit getPredsinStmtPath(Unit u);

	public Unit getStmtPathTail();

	public List<StmtPoint> getStmtPath();
}
