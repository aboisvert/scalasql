package scalasql.query

import scalasql.core.{Context, LiveSqlExprs, Expr, SqlStr}

trait SelectBase {
  protected def selectLhsMap(prevContext: Context): Map[Expr.Identity, SqlStr]
  protected def selectRenderer(prevContext: Context): SelectBase.Renderer
}
object SelectBase {
  def lhsMap(s: SelectBase, prevContext: Context) = s.selectLhsMap(prevContext)
  def renderer(s: SelectBase, prevContext: Context) = s.selectRenderer(prevContext)

  trait Renderer {
    def render(liveExprs: LiveSqlExprs): SqlStr
  }

}
