; ModuleID = 'testb.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
@value = global i32 0		; <i32*> [#uses=4]
@.str = internal constant [4 x i8] c"%d\0A\00"		; <[4 x i8]*> [#uses=1]

define void @test(i32 %mm) nounwind {
entry:
	%0 = icmp sgt i32 %mm, 0		; <i1> [#uses=1]
	br i1 %0, label %bb, label %bb2

bb:		; preds = %bb, %entry
	%i.03 = phi i32 [ 0, %entry ], [ %5, %bb ]		; <i32> [#uses=2]
	%ptr.04.rec = phi i32 [ 0, %entry ], [ %.rec, %bb ]		; <i32> [#uses=2]
	%ptr.04.sum = add i32 %ptr.04.rec, %i.03		; <i32> [#uses=1]
	%1 = getelementptr i32* @value, i32 %ptr.04.sum		; <i32*> [#uses=1]
	%2 = load i32* %1, align 4		; <i32> [#uses=1]
	%3 = load i32* @value, align 4		; <i32> [#uses=1]
	%4 = add i32 %3, %2		; <i32> [#uses=1]
	store i32 %4, i32* @value, align 4
	%5 = add i32 %i.03, 1		; <i32> [#uses=3]
	%.rec = add i32 %ptr.04.rec, %5		; <i32> [#uses=1]
	%exitcond5 = icmp eq i32 %5, %mm		; <i1> [#uses=1]
	br i1 %exitcond5, label %bb2, label %bb

bb2:		; preds = %bb, %entry
	%6 = load i32* @value, align 4		; <i32> [#uses=1]
	%7 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32 %6) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind