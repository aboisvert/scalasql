package scalasql.dialects

import scalasql.core.{Expr, WithSqlExpr}
import scalasql.query._

trait OnConflictOps {
  implicit def OnConflictableInsertValues[V[_[_]], R](
      query: InsertColumns[V, R]
  ): OnConflict[V[Column], Int] =
    new OnConflict[V[Column], Int](query, WithSqlExpr.get(query), query.table)

  implicit def OnConflictableInsertSelect[V[_[_]], C, R, R2](
      query: InsertSelect[V, C, R, R2]
  ): OnConflict[V[Expr], Int] = {
    new OnConflict[V[Expr], Int](query, WithSqlExpr.get(query), query.table)
  }

}
