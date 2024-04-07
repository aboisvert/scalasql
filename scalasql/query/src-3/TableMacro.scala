package scalasql.query

import scala.quoted.*
import scalasql.query.Table.Metadata
import scalasql.core.DialectTypeMappers
import scalasql.core.Queryable
import scalasql.core.{Sc, TypeMapper}
import scalasql.core.{Expr => SqlExpr}
import scalasql.core.Queryable.Row
import scalasql.core.Queryable.ResultSetIterator

object TableMacros:

  /** Generates Table.Metadata for `object SomeTable extends Table[SomeTable]` */
  def metadataImpl[V[_[_]] : Type](using Quotes): Expr[Table.Metadata[V]] =
    import quotes.reflect.*

    /** Returns the human-readable type name of a TypeRepr; used for error-reporting. */
    def fullTypeName(tpe: TypeRepr): String = tpe match
      // Note: match is not exhaustive -- doesn't handle Scala's array of fancy types
      case t: NamedType =>
        t.name
      case o: OrType =>
        fullTypeName(o.left) + " | " + fullTypeName(o.right)
      case o: AndType =>
        fullTypeName(o.left) + " & " + fullTypeName(o.right)
      case AppliedType(base, args) =>
        fullTypeName(base) + args.map(fullTypeName).mkString("[", ",", "]")

    val classSymbol = TypeRepr.of[V[Column]].classSymbol.get
    val constructor = classSymbol.primaryConstructor
    val constructorTypeParameters = constructor.paramSymss(0)
    val constructorParameters = constructor.paramSymss(1)

    def columnParams(tableRef: Expr[TableRef]) =
      // TODO if isTypeParamType
      for param <- constructorParameters yield
        val nameExpr = Expr(param.name)
        param.typeRef.translucentSuperType match
          case AppliedType(_, List(tp)) => tp.asType match
            case '[t] =>
              Expr.summon[TypeMapper[t]] match
                case Some(mappedType) =>
                  '{ Column[t]($tableRef, Table.columnNameOverride($tableRef.value)($nameExpr))($mappedType) }.asTerm
                case None =>
                  report.errorAndAbort(s"TypeMapper[${fullTypeName(tp)}] not found.", Position.ofMacroExpansion)

    def constructorCall__(tableRef: Expr[TableRef]) =
      val ownerType = TypeTree.of[V[Column]]
      val ownerTypeArgs = ownerType.tpe.typeArgs
      val baseConstructorTerm = Select(New(ownerType), constructor)
      val typeAppliedConstructorTerm = TypeApply(baseConstructorTerm, ownerTypeArgs.map(t => TypeTree.ref(t.typeSymbol)))
      Apply(typeAppliedConstructorTerm, columnParams(tableRef)).asExprOf[V[Column]]

    def constructorCall[T[_] : Type](params: List[Term]) =
      val ownerType = TypeTree.of[V[T]]
      val ownerTypeArgs = ownerType.tpe.typeArgs
      val baseConstructorTerm = Select(New(ownerType), constructor)
      val typeAppliedConstructorTerm = TypeApply(baseConstructorTerm, ownerTypeArgs.map(t => TypeTree.ref(t.typeSymbol)))
      Apply(typeAppliedConstructorTerm, params).asExprOf[V[T]]

    def subParam[T[_] : Type](tp: TypeRef) =
      tp.translucentSuperType match
        case AppliedType(_, List(t)) =>
          t.asType match
            case '[t] => TypeRepr.of[T[t]]

    def queryables =
      Expr.ofList(
        for param <- constructorParameters yield
          // report.info(s"param: ${param.name}", Position.ofMacroExpansion)
          val tpe1 = subParam[Sc](param.typeRef)
          val tpe2 = subParam[SqlExpr](param.typeRef)
          (tpe1.asType, tpe2.asType) match
            case ('[t1], '[t2]) => Expr.summon[Row[t2, t1]].getOrElse({
              report.errorAndAbort(
                s"Queryable.Row[${fullTypeName(tpe2)}, ${fullTypeName(tpe1)}] not found.",
                Position.ofMacroExpansion)
            }) //.asTerm
      )

    val labels = Expr(constructorParameters.map(_.name)) // TODO isTypeParamType

    def flattenExprs(queryable: Expr[Metadata.QueryableProxy], table: Expr[V[SqlExpr]]) =
      val exprs =
        for (param, i) <- constructorParameters.zipWithIndex yield
          val iExpr = Expr(i)
          val tpe = subParam[Sc](param.typeRef)
          val tpe2 = subParam[SqlExpr](param.typeRef)
          (tpe.asType, tpe2.asType) match
            case ('[t1], '[t2]) =>
              val q = Select(table.asTerm, classSymbol.fieldMember(param.name)).asExprOf[t2]
              '{ $queryable.apply[t2, t1]($iExpr).walkExprs($q) }
      exprs.reduceLeft: (l, r) =>
        '{ $l ++ $r }

    def construct(queryable: Expr[Metadata.QueryableProxy], args: Expr[ResultSetIterator]) =
      val ownerType = TypeTree.of[V[Sc]]
      val constructor = ownerType.tpe.classSymbol.get.primaryConstructor
      val constructorParameters = constructor.paramSymss(1)

      val params = for (param, i) <- constructorParameters.zipWithIndex yield
        val iExpr = Expr(i)
        val tpe = subParam[Sc](param.typeRef)
        val tpe2 = subParam[SqlExpr](param.typeRef)
        (tpe.asType, tpe2.asType) match
          case ('[t1], '[t2]) =>
            '{ $queryable.apply[t2, t1]($iExpr).construct($args) : Sc[t1] }.asTerm

      val baseConstructorTerm = Select(New(ownerType), constructor)
      val typeAppliedConstructorTerm = TypeApply(baseConstructorTerm, List(TypeTree.of[Sc]))
      Apply(typeAppliedConstructorTerm, params).asExprOf[V[Sc]]

    def deconstruct(queryable: Expr[Metadata.QueryableProxy], table: Expr[V[Sc]]) =
      val ownerType = TypeTree.of[V[SqlExpr]]
      val constructor = ownerType.tpe.classSymbol.get.primaryConstructor
      val constructorParameters = constructor.paramSymss(1)

      val params = for (param, i) <- constructorParameters.zipWithIndex yield
        val iExpr = Expr(i)
        val tpe = subParam[Sc](param.typeRef)
        val tpe2 = subParam[SqlExpr](param.typeRef)
        (tpe.asType, tpe2.asType) match
          case ('[t1], '[t2]) =>
            val r = Select(table.asTerm, classSymbol.fieldMember(param.name)).asExprOf[t1]
            '{ $queryable.apply[t2, t1]($iExpr).deconstruct($r) }.asTerm

      val baseConstructorTerm = Select(New(ownerType), constructor)
      val typeAppliedConstructorTerm = TypeApply(baseConstructorTerm, List(TypeTree.of[SqlExpr]))
      Apply(typeAppliedConstructorTerm, params).asExprOf[V[SqlExpr]]

    val queryablesExpr = '{
      (dialect: DialectTypeMappers, i: Int) =>
        import dialect.given
        $queryables(i)
    }

    val walkLabelsExpr = '{ () => $labels }

    val queryableExpr = '{
      (walkLabels0: () => Seq[String], dialect: DialectTypeMappers, queryable: Metadata.QueryableProxy) =>
        import dialect.given
        Table.Internal.TableQueryable[V[SqlExpr], V[Sc]](
          walkLabels0,
          walkExprs0 = (table: V[SqlExpr]) => ${ flattenExprs('queryable, 'table) },
          construct0 = (args: ResultSetIterator) => ${ construct('queryable, 'args) },
          deconstruct0 = (r: V[Sc]) => ${ deconstruct('queryable, 'r) }
        )
    }

    val vExpr0 = '{
      (tableRef: TableRef, dialect: DialectTypeMappers, queryable: Metadata.QueryableProxy) =>
        import dialect.given
        ${ constructorCall__('tableRef) }
    }

    '{ Metadata($queryablesExpr, $walkLabelsExpr, $queryableExpr, $vExpr0) }


trait TableMacros:
  inline given metadata[V[_[_]]]: Table.Metadata[V] = ${ TableMacros.metadataImpl[V] }
