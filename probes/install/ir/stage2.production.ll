; ModuleID = 'kernel/json/stage2.c'
source_filename = "kernel/json/stage2.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.EPow = type { i64, i64, i32 }
%struct.Stk = type { %struct.StkBn, %struct.StkBn, i64, i32 }
%struct.StkBn = type { [96 x i64], i32 }

@.str.17 = private unnamed_addr constant [5 x i8] c"true\00", align 1
@.str.18 = private unnamed_addr constant [6 x i8] c"false\00", align 1
@.str.19 = private unnamed_addr constant [5 x i8] c"null\00", align 1
@NUMF_EL1_P10 = internal unnamed_addr constant [20 x i64] [i64 1, i64 10, i64 100, i64 1000, i64 10000, i64 100000, i64 1000000, i64 10000000, i64 100000000, i64 1000000000, i64 10000000000, i64 100000000000, i64 1000000000000, i64 10000000000000, i64 100000000000000, i64 1000000000000000, i64 10000000000000000, i64 100000000000000000, i64 1000000000000000000, i64 -8446744073709551616], align 16
@NUMF_EL1_POW10 = internal unnamed_addr constant [23 x double] [double 1.000000e+00, double 1.000000e+01, double 1.000000e+02, double 1.000000e+03, double 1.000000e+04, double 1.000000e+05, double 1.000000e+06, double 1.000000e+07, double 1.000000e+08, double 1.000000e+09, double 1.000000e+10, double 1.000000e+11, double 1.000000e+12, double 1.000000e+13, double 1.000000e+14, double 1.000000e+15, double 1.000000e+16, double 1.000000e+17, double 1.000000e+18, double 1.000000e+19, double 1.000000e+20, double 1.000000e+21, double 1.000000e+22], align 16
@g_nume1_el = internal unnamed_addr global i64 0, align 8
@g_nume1_slow = internal unnamed_addr global i64 0, align 8
@g_el_window = internal unnamed_addr global i64 0, align 8
@EPOW = internal unnamed_addr constant [91 x { i64, i64, i32, [4 x i8] }] [{ i64, i64, i32, [4 x i8] } { i64 -5282707615139903279, i64 4422670725869800738, i32 -277, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -1991698500497491195, i64 -8306719647944912790, i32 -274, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -8162340590452013853, i64 8643358275316593218, i32 -270, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -5591239719637629412, i64 6192511825718353619, i32 -267, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -2377363631119648861, i64 7740639782147942024, i32 -264, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -8403381297090862394, i64 2532056854628769813, i32 -260, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -5892540602936190089, i64 -6058300968568813542, i32 -257, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -2753989735242849707, i64 -7572876210711016927, i32 -254, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -8638772612167862923, i64 9102010423587778132, i32 -250, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -6186779746782440750, i64 -2457545025797441047, i32 -247, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -3121788665050663033, i64 -7683617300674189212, i32 -244, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -8868646943297746252, i64 -4802260812921368258, i32 -240, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -6474122660694794911, i64 -1391139997724322418, i32 -237, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -3480967307441105734, i64 7484447039699372786, i32 -234, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -9093133594791772940, i64 -9157278655470055721, i32 -230, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -6754730975062328271, i64 -6834912300910181747, i32 -227, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -3831727700400522434, i64 679731660717048624, i32 -224, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -177973607073265139, i64 -8373707460958465028, i32 -221, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -7028762532061872568, i64 8601490892183123069, i32 -217, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -4174267146649952806, i64 -7694880458480647779, i32 -214, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -606147914885053103, i64 4216457482181353988, i32 -211, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -7296371474444240046, i64 -4282243101277735614, i32 -207, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -4508778324627912153, i64 8482254178684994195, i32 -204, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -1024286887357502287, i64 5991131704928854840, i32 -201, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -7557708332239520786, i64 -3173071712060547581, i32 -197, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -4835449396872013078, i64 -8578025658503072380, i32 -194, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -1432625727662628443, i64 3112525982153323237, i32 -191, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -7812920107430224633, i64 4251171748059520975, i32 -187, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -5154464115860392887, i64 702278666647013314, i32 -184, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -1831394126398103205, i64 5489534351736154547, i32 -181, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -8062150356639896359, i64 1125115960621402640, i32 -177, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -5466001927372482545, i64 6018080969204141204, i32 -174, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -2220816390788215277, i64 2910915193077788601, i32 -171, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -8305539271883716405, i64 -486521013540076077, i32 -167, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -5770238071427257602, i64 -608151266925095096, i32 -164, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -2601111570856684098, i64 -5371875102083756773, i32 -161, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -8543223759426509417, i64 3560107088838733872, i32 -157, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -6067343680855748868, i64 -161552157378970563, i32 -154, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -2972493582642298180, i64 4409745821703674700, i32 -151, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -8775337516792518219, i64 -6467280898289979121, i32 -147, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -6357485877563259869, i64 1139270913992301907, i32 -144, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -3335171328526686933, i64 -3187597375937010520, i32 -141, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -9002011107970261189, i64 7231123676894144233, i32 -137, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -6640827866535438582, i64 4427218577690292387, i32 -134, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -3689348814741910324, i64 -3689348814741910324, i32 -131, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -9223372036854775808, i64 0, i32 -127, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -6917529027641081856, i64 0, i32 -124, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -4035225266123964416, i64 0, i32 -121, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -432345564227567616, i64 0, i32 -118, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -7187745005283311616, i64 0, i32 -114, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -4372995238176751616, i64 0, i32 -111, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -854558029293551616, i64 0, i32 -108, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -7451627795949551616, i64 0, i32 -104, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -4702848726509551616, i64 0, i32 -101, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -1266874889709551616, i64 0, i32 -98, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -7709325833709551616, i64 0, i32 -94, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -5024971273709551616, i64 0, i32 -91, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -1669528073709551616, i64 0, i32 -88, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -7960984073709551616, i64 0, i32 -84, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -5339544073709551616, i64 0, i32 -81, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -2062744073709551616, i64 0, i32 -78, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -8206744073709551616, i64 0, i32 -74, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -5646744073709551616, i64 0, i32 -71, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -2446744073709551616, i64 0, i32 -68, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -8446744073709551616, i64 0, i32 -64, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -5946744073709551616, i64 0, i32 -61, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -2821744073709551616, i64 0, i32 -58, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -8681119073709551616, i64 0, i32 -54, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -6239712823709551616, i64 0, i32 -51, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -3187955011209551616, i64 0, i32 -48, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -8910000909647051616, i64 0, i32 -44, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -6525815118631426616, i64 0, i32 -41, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -3545582879861895366, i64 0, i32 -38, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -9133518327554766460, i64 4611686018427387904, i32 -34, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -6805211891016070171, i64 5764607523034234880, i32 -31, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -3894828845342699810, i64 -6629298651489370112, i32 -28, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -256850038250986858, i64 5548434740920451072, i32 -25, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -7078060301547948643, i64 -1143914305352105984, i32 -21, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -4235889358507547899, i64 7793479155164643328, i32 -18, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -683175679707046970, i64 -4093209111326359552, i32 -15, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -7344513827457986212, i64 4359273333062107136, i32 -11, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -4568956265895094861, i64 5449091666327633920, i32 -8, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -1099509313941480672, i64 2199678564482154496, i32 -5, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -7604722348854507276, i64 1374799102801346560, i32 -1, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -4894216917640746191, i64 1718498878501683200, i32 2, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -1506085128623544835, i64 6759809616554491904, i32 5, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -7858832233030797378, i64 6530724019560251392, i32 9, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -5211854272861108819, i64 -1059967012404461568, i32 12, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -1903131822648998119, i64 7898413271349198848, i32 15, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -8106986416796705681, i64 -1981020733047832576, i32 19, [4 x i8] zeroinitializer }, { i64, i64, i32, [4 x i8] } { i64 -5522047002568494197, i64 -2476275916309790720, i32 22, [4 x i8] zeroinitializer }], align 16
@g_el_undec = internal unnamed_addr global i64 0, align 8
@g_el_range = internal unnamed_addr global i64 0, align 8
@STK_P5 = internal unnamed_addr constant [27 x i64] [i64 1, i64 5, i64 25, i64 125, i64 625, i64 3125, i64 15625, i64 78125, i64 390625, i64 1953125, i64 9765625, i64 48828125, i64 244140625, i64 1220703125, i64 6103515625, i64 30517578125, i64 152587890625, i64 762939453125, i64 3814697265625, i64 19073486328125, i64 95367431640625, i64 476837158203125, i64 2384185791015625, i64 11920928955078125, i64 59604644775390625, i64 298023223876953125, i64 1490116119384765625], align 16

; Function Attrs: nounwind sspstrong uwtable
define range(i64 0, 2) i64 @leanllvm_json_stage2(ptr noundef %0, i64 noundef %1, ptr noundef readonly captures(none) %2, i64 noundef %3, ptr noundef %4, i64 noundef %5, ptr noundef %6, i64 noundef %7, ptr noundef captures(none) %8, ptr noundef %9, i64 noundef %10, ptr noundef captures(none) %11, ptr noundef writeonly captures(none) %12) local_unnamed_addr #0 align 64 {
  %14 = alloca double, align 8
  %15 = alloca i64, align 8
  %16 = alloca double, align 8
  %17 = alloca i64, align 8
  %18 = alloca i64, align 8
  %19 = alloca [520 x i8], align 16
  %20 = alloca [520 x i8], align 16
  %21 = alloca i64, align 8
  %22 = load i64, ptr %8, align 8, !tbaa !6
  %23 = load i64, ptr %11, align 8, !tbaa !6
  call void @llvm.lifetime.start.p0(i64 520, ptr nonnull %19) #11
  call void @llvm.lifetime.start.p0(i64 520, ptr nonnull %20) #11
  call void @llvm.lifetime.start.p0(i64 8, ptr nonnull %21) #11
  store i64 0, ptr %21, align 8, !tbaa !6
  %24 = getelementptr i8, ptr %0, i64 -1
  %25 = icmp eq i64 %3, 0
  br i1 %25, label %1162, label %26

26:                                               ; preds = %13, %1146
  %27 = phi i64 [ %1147, %1146 ], [ 0, %13 ]
  %28 = phi i32 [ %1148, %1146 ], [ 0, %13 ]
  %29 = phi i32 [ %1149, %1146 ], [ 0, %13 ]
  %30 = phi i64 [ %1150, %1146 ], [ %22, %13 ]
  %31 = phi i64 [ %1151, %1146 ], [ %23, %13 ]
  %32 = phi i64 [ %1152, %1146 ], [ %23, %13 ]
  %33 = add nuw i64 %27, 1
  %34 = getelementptr inbounds nuw i32, ptr %2, i64 %27
  %35 = load i32, ptr %34, align 4, !tbaa !10
  %36 = zext i32 %35 to i64
  %37 = getelementptr inbounds nuw i8, ptr %0, i64 %36
  %38 = load i8, ptr %37, align 1, !tbaa !12
  switch i8 %38, label %227 [
    i8 123, label %39
    i8 91, label %39
    i8 125, label %71
    i8 93, label %71
    i8 44, label %106
    i8 58, label %122
    i8 34, label %135
  ]

39:                                               ; preds = %26, %26
  %40 = icmp eq i32 %28, 0
  br i1 %40, label %41, label %43

41:                                               ; preds = %39
  %42 = icmp eq i32 %29, 0
  br i1 %42, label %58, label %1162

43:                                               ; preds = %39
  %44 = add i32 %28, -1
  %45 = zext i32 %44 to i64
  %46 = getelementptr inbounds nuw i8, ptr %19, i64 %45
  %47 = load i8, ptr %46, align 1, !tbaa !12
  %48 = icmp eq i8 %47, 1
  %49 = getelementptr inbounds nuw i8, ptr %20, i64 %45
  %50 = load i8, ptr %49, align 1, !tbaa !12
  br i1 %48, label %51, label %55

51:                                               ; preds = %43
  %52 = icmp ne i8 %50, 2
  %53 = icmp ugt i32 %28, 519
  %54 = select i1 %52, i1 true, i1 %53
  br i1 %54, label %1162, label %58

55:                                               ; preds = %43
  switch i8 %50, label %1162 [
    i8 0, label %56
    i8 2, label %56
  ]

56:                                               ; preds = %55, %55
  %57 = icmp ugt i32 %28, 519
  br i1 %57, label %1162, label %58

58:                                               ; preds = %51, %41, %56
  %59 = icmp eq i8 %38, 123
  %60 = select i1 %59, i8 1, i8 2
  %61 = zext nneg i32 %28 to i64
  %62 = getelementptr inbounds nuw [520 x i8], ptr %19, i64 0, i64 %61
  store i8 %60, ptr %62, align 1, !tbaa !12
  %63 = getelementptr inbounds nuw [520 x i8], ptr %20, i64 0, i64 %61
  store i8 0, ptr %63, align 1, !tbaa !12
  %64 = add i64 %31, 1
  %65 = icmp ugt i64 %64, %10
  br i1 %65, label %66, label %67

66:                                               ; preds = %58
  call void @llvm.trap()
  unreachable

67:                                               ; preds = %58
  %68 = select i1 %59, i8 1, i8 3
  %69 = add nuw nsw i32 %28, 1
  %70 = getelementptr inbounds nuw i8, ptr %9, i64 %31
  store i8 %68, ptr %70, align 1
  br label %1138

71:                                               ; preds = %26, %26
  %72 = icmp eq i32 %28, 0
  br i1 %72, label %1162, label %73

73:                                               ; preds = %71
  %74 = add i32 %28, -1
  %75 = icmp eq i8 %38, 125
  %76 = select i1 %75, i32 1, i32 2
  %77 = zext i32 %74 to i64
  %78 = getelementptr inbounds nuw [520 x i8], ptr %19, i64 0, i64 %77
  %79 = load i8, ptr %78, align 1, !tbaa !12
  %80 = zext i8 %79 to i32
  %81 = icmp eq i32 %76, %80
  br i1 %81, label %82, label %1162

82:                                               ; preds = %73
  %83 = getelementptr inbounds nuw [520 x i8], ptr %20, i64 0, i64 %77
  %84 = load i8, ptr %83, align 1, !tbaa !12
  br i1 %75, label %85, label %86

85:                                               ; preds = %82
  switch i8 %84, label %1162 [
    i8 3, label %88
    i8 0, label %88
  ]

86:                                               ; preds = %82
  %87 = icmp ult i8 %84, 2
  br i1 %87, label %88, label %1162

88:                                               ; preds = %85, %85, %86
  %89 = icmp eq i32 %74, 0
  br i1 %89, label %98, label %90

90:                                               ; preds = %88
  %91 = add i32 %28, -2
  %92 = zext i32 %91 to i64
  %93 = getelementptr inbounds nuw i8, ptr %19, i64 %92
  %94 = load i8, ptr %93, align 1, !tbaa !12
  %95 = icmp eq i8 %94, 1
  %96 = select i1 %95, i8 3, i8 1
  %97 = getelementptr inbounds nuw i8, ptr %20, i64 %92
  store i8 %96, ptr %97, align 1, !tbaa !12
  br label %98

98:                                               ; preds = %90, %88
  %99 = phi i32 [ 1, %88 ], [ %29, %90 ]
  %100 = add i64 %31, 1
  %101 = icmp ugt i64 %100, %10
  br i1 %101, label %102, label %103

102:                                              ; preds = %98
  call void @llvm.trap()
  unreachable

103:                                              ; preds = %98
  %104 = select i1 %75, i8 2, i8 4
  %105 = getelementptr inbounds nuw i8, ptr %9, i64 %31
  store i8 %104, ptr %105, align 1
  br label %1138

106:                                              ; preds = %26
  %107 = icmp eq i32 %28, 0
  br i1 %107, label %1162, label %108

108:                                              ; preds = %106
  %109 = add i32 %28, -1
  %110 = zext i32 %109 to i64
  %111 = getelementptr inbounds nuw [520 x i8], ptr %19, i64 0, i64 %110
  %112 = load i8, ptr %111, align 1, !tbaa !12
  %113 = icmp eq i8 %112, 1
  %114 = getelementptr inbounds nuw [520 x i8], ptr %20, i64 0, i64 %110
  %115 = load i8, ptr %114, align 1, !tbaa !12
  br i1 %113, label %116, label %119

116:                                              ; preds = %108
  %117 = icmp eq i8 %115, 3
  br i1 %117, label %118, label %1162

118:                                              ; preds = %116
  store i8 4, ptr %114, align 1, !tbaa !12
  br label %1138

119:                                              ; preds = %108
  %120 = icmp eq i8 %115, 1
  br i1 %120, label %121, label %1162

121:                                              ; preds = %119
  store i8 2, ptr %114, align 1, !tbaa !12
  br label %1138

122:                                              ; preds = %26
  %123 = icmp eq i32 %28, 0
  br i1 %123, label %1162, label %124

124:                                              ; preds = %122
  %125 = add i32 %28, -1
  %126 = zext i32 %125 to i64
  %127 = getelementptr inbounds nuw [520 x i8], ptr %19, i64 0, i64 %126
  %128 = load i8, ptr %127, align 1, !tbaa !12
  %129 = icmp eq i8 %128, 1
  br i1 %129, label %130, label %1162

130:                                              ; preds = %124
  %131 = getelementptr inbounds nuw [520 x i8], ptr %20, i64 0, i64 %126
  %132 = load i8, ptr %131, align 1, !tbaa !12
  %133 = icmp eq i8 %132, 1
  br i1 %133, label %134, label %1162

134:                                              ; preds = %130
  store i8 2, ptr %131, align 1, !tbaa !12
  br label %1138

135:                                              ; preds = %26
  %136 = icmp ult i64 %33, %3
  br i1 %136, label %137, label %1162

137:                                              ; preds = %135
  %138 = add nuw i64 %27, 2
  %139 = getelementptr inbounds nuw i32, ptr %2, i64 %33
  %140 = load i32, ptr %139, align 4, !tbaa !10
  %141 = zext i32 %140 to i64
  %142 = icmp ugt i64 %1, %141
  br i1 %142, label %143, label %1162

143:                                              ; preds = %137
  %144 = icmp eq i32 %28, 0
  br i1 %144, label %153, label %145

145:                                              ; preds = %143
  %146 = add i32 %28, -1
  %147 = zext i32 %146 to i64
  %148 = getelementptr inbounds nuw i8, ptr %19, i64 %147
  %149 = load i8, ptr %148, align 1, !tbaa !12
  %150 = icmp eq i8 %149, 1
  %151 = getelementptr inbounds nuw i8, ptr %20, i64 %147
  %152 = load i8, ptr %151, align 1, !tbaa !12
  br i1 %150, label %158, label %155

153:                                              ; preds = %143
  %154 = icmp eq i32 %29, 0
  br label %162

155:                                              ; preds = %145
  %156 = and i8 %152, -3
  %157 = icmp eq i8 %156, 0
  br label %162

158:                                              ; preds = %145
  %159 = icmp eq i8 %152, 2
  %160 = and i8 %152, -5
  %161 = icmp eq i8 %160, 0
  br label %162

162:                                              ; preds = %155, %153, %158
  %163 = phi i1 [ %159, %158 ], [ %157, %155 ], [ %154, %153 ]
  %164 = phi i1 [ %161, %158 ], [ false, %155 ], [ false, %153 ]
  %165 = select i1 %164, i1 true, i1 %163
  br i1 %165, label %166, label %1162

166:                                              ; preds = %162
  %167 = xor i64 %36, -1
  %168 = add nsw i64 %141, %167
  %169 = add nsw i64 %168, 64
  %170 = add i64 %169, %30
  %171 = icmp ugt i64 %170, %7
  br i1 %171, label %172, label %173

172:                                              ; preds = %166
  call void @llvm.trap()
  unreachable

173:                                              ; preds = %166
  %174 = getelementptr inbounds nuw i8, ptr %6, i64 %30
  %175 = getelementptr inbounds nuw i8, ptr %37, i64 1
  %176 = add nuw nsw i64 %36, 1
  %177 = load i64, ptr %21, align 8, !tbaa !6
  %178 = icmp ult i64 %177, %5
  br i1 %178, label %179, label %192

179:                                              ; preds = %173, %184
  %180 = phi i64 [ %185, %184 ], [ %177, %173 ]
  %181 = getelementptr inbounds nuw i32, ptr %4, i64 %180
  %182 = load i32, ptr %181, align 4, !tbaa !10
  %183 = icmp ult i32 %35, %182
  br i1 %183, label %187, label %184

184:                                              ; preds = %179
  %185 = add i64 %180, 1
  store i64 %185, ptr %21, align 8, !tbaa !6
  %186 = icmp eq i64 %185, %5
  br i1 %186, label %192, label %179, !llvm.loop !13

187:                                              ; preds = %179
  %188 = icmp ugt i32 %140, %182
  br i1 %188, label %189, label %192

189:                                              ; preds = %187
  call void @llvm.lifetime.start.p0(i64 8, ptr nonnull %18) #11
  store i64 0, ptr %18, align 8, !tbaa !6
  %190 = call i64 @leanllvm_json_escape_expand(ptr noundef nonnull %175, i64 noundef range(i64 -4294967296, 4294967295) %168, ptr noundef %174, ptr noundef nonnull %18, ptr noundef nonnull %4, ptr noundef nonnull %21, i64 noundef %5, i64 noundef %176) #11
  %191 = icmp eq i64 %190, -1
  br i1 %191, label %224, label %196

192:                                              ; preds = %184, %173, %187
  %193 = add i32 %35, 1
  %194 = zext i32 %193 to i64
  %195 = or disjoint i64 %194, -9223372036854775808
  br label %198

196:                                              ; preds = %189
  call void @llvm.lifetime.end.p0(i64 8, ptr nonnull %18) #11
  %197 = add i64 %30, %190
  br label %198

198:                                              ; preds = %196, %192
  %199 = phi i64 [ %190, %196 ], [ %168, %192 ]
  %200 = phi i64 [ %30, %196 ], [ %195, %192 ]
  %201 = phi i64 [ %197, %196 ], [ %30, %192 ]
  %202 = add i64 %31, 13
  %203 = icmp ugt i64 %202, %10
  br i1 %203, label %204, label %205

204:                                              ; preds = %198
  call void @llvm.trap()
  unreachable

205:                                              ; preds = %198
  %206 = trunc i64 %199 to i32
  %207 = getelementptr inbounds nuw i8, ptr %9, i64 %31
  %208 = select i1 %164, i8 5, i8 6
  store i8 %208, ptr %207, align 1, !tbaa !12
  %209 = getelementptr inbounds nuw i8, ptr %207, i64 1
  store i32 %206, ptr %209, align 1
  %210 = getelementptr inbounds nuw i8, ptr %207, i64 5
  store i64 %200, ptr %210, align 1
  br i1 %164, label %211, label %215

211:                                              ; preds = %205
  %212 = add i32 %28, -1
  %213 = zext i32 %212 to i64
  %214 = getelementptr inbounds nuw [520 x i8], ptr %20, i64 0, i64 %213
  store i8 1, ptr %214, align 1, !tbaa !12
  br label %1138

215:                                              ; preds = %205
  br i1 %144, label %1153, label %216

216:                                              ; preds = %215
  %217 = add i32 %28, -1
  %218 = zext i32 %217 to i64
  %219 = getelementptr inbounds nuw i8, ptr %19, i64 %218
  %220 = load i8, ptr %219, align 1, !tbaa !12
  %221 = icmp eq i8 %220, 1
  %222 = select i1 %221, i8 3, i8 1
  %223 = getelementptr inbounds nuw i8, ptr %20, i64 %218
  store i8 %222, ptr %223, align 1, !tbaa !12
  br label %1138

224:                                              ; preds = %189
  %225 = load i64, ptr %18, align 8, !tbaa !6
  %226 = add i64 %225, %176
  call void @llvm.lifetime.end.p0(i64 8, ptr nonnull %18) #11
  br label %1162

227:                                              ; preds = %26
  %228 = icmp ult i64 %33, %3
  br i1 %228, label %229, label %233

229:                                              ; preds = %227
  %230 = getelementptr inbounds nuw i32, ptr %2, i64 %33
  %231 = load i32, ptr %230, align 4, !tbaa !10
  %232 = zext i32 %231 to i64
  br label %233

233:                                              ; preds = %229, %227
  %234 = phi i64 [ %232, %229 ], [ %1, %227 ]
  %235 = icmp ugt i64 %234, %36
  br i1 %235, label %236, label %247

236:                                              ; preds = %233
  %237 = getelementptr i8, ptr %24, i64 %234
  %238 = load i8, ptr %237, align 1, !tbaa !12
  switch i8 %238, label %247 [
    i8 32, label %239
    i8 13, label %239
    i8 10, label %239
    i8 9, label %239
  ]

239:                                              ; preds = %236, %236, %236, %236
  br label %240

240:                                              ; preds = %239, %244
  %241 = phi i64 [ %245, %244 ], [ %36, %239 ]
  %242 = getelementptr inbounds nuw i8, ptr %0, i64 %241
  %243 = load i8, ptr %242, align 1, !tbaa !12
  switch i8 %243, label %244 [
    i8 32, label %247
    i8 13, label %247
    i8 10, label %247
    i8 9, label %247
  ]

244:                                              ; preds = %240
  %245 = add nuw i64 %241, 1
  %246 = icmp eq i64 %245, %234
  br i1 %246, label %247, label %240, !llvm.loop !15

247:                                              ; preds = %244, %240, %240, %240, %240, %233, %236
  %248 = phi i64 [ %234, %236 ], [ %36, %233 ], [ %234, %244 ], [ %241, %240 ], [ %241, %240 ], [ %241, %240 ], [ %241, %240 ]
  %249 = icmp eq i8 %38, 45
  %250 = add i8 %38, -48
  %251 = icmp ult i8 %250, 10
  %252 = or i1 %249, %251
  br i1 %252, label %257, label %253

253:                                              ; preds = %247
  switch i8 %38, label %256 [
    i8 116, label %257
    i8 102, label %254
    i8 110, label %255
  ]

254:                                              ; preds = %253
  br label %257

255:                                              ; preds = %253
  br label %257

256:                                              ; preds = %253
  br label %257

257:                                              ; preds = %253, %247, %256, %255, %254
  %258 = phi i32 [ 0, %256 ], [ 9, %254 ], [ 10, %255 ], [ 7, %247 ], [ 8, %253 ]
  %259 = icmp eq i32 %28, 0
  br i1 %259, label %260, label %262

260:                                              ; preds = %257
  %261 = icmp eq i32 %29, 0
  br i1 %261, label %273, label %1162

262:                                              ; preds = %257
  %263 = add i32 %28, -1
  %264 = zext i32 %263 to i64
  %265 = getelementptr inbounds nuw i8, ptr %19, i64 %264
  %266 = load i8, ptr %265, align 1, !tbaa !12
  %267 = icmp eq i8 %266, 1
  %268 = getelementptr inbounds nuw i8, ptr %20, i64 %264
  %269 = load i8, ptr %268, align 1, !tbaa !12
  br i1 %267, label %270, label %272

270:                                              ; preds = %262
  %271 = icmp eq i8 %269, 2
  br i1 %271, label %273, label %1162

272:                                              ; preds = %262
  switch i8 %269, label %1162 [
    i8 0, label %273
    i8 2, label %273
  ]

273:                                              ; preds = %272, %272, %270, %260
  switch i32 %258, label %677 [
    i32 0, label %710
    i32 7, label %274
  ]

274:                                              ; preds = %273
  call void @llvm.lifetime.start.p0(i64 8, ptr nonnull %17) #11
  %275 = sub i64 %248, %36
  %276 = icmp ne i64 %248, %36
  %277 = icmp eq i8 %38, 45
  %278 = and i1 %276, %277
  %279 = zext i1 %278 to i64
  %280 = icmp ugt i64 %275, %279
  br i1 %280, label %281, label %664

281:                                              ; preds = %274
  %282 = getelementptr inbounds nuw i8, ptr %37, i64 %279
  %283 = load i8, ptr %282, align 1, !tbaa !12
  %284 = icmp eq i8 %283, 48
  br i1 %284, label %285, label %287

285:                                              ; preds = %281
  %286 = select i1 %278, i64 2, i64 1
  br label %363

287:                                              ; preds = %281
  %288 = add i8 %283, -49
  %289 = icmp ult i8 %288, 9
  br i1 %289, label %290, label %664

290:                                              ; preds = %287
  %291 = and i8 %283, 15
  %292 = zext nneg i8 %291 to i64
  %293 = select i1 %278, i64 2, i64 1
  %294 = or disjoint i64 %293, 8
  %295 = icmp ugt i64 %294, %275
  br i1 %295, label %338, label %296

296:                                              ; preds = %290
  %297 = getelementptr inbounds nuw i8, ptr %37, i64 %293
  %298 = load i64, ptr %297, align 1
  %299 = insertelement <2 x i64> <i64 poison, i64 0>, i64 %298, i64 0
  %300 = bitcast <2 x i64> %299 to <16 x i8>
  %301 = add <16 x i8> %300, splat (i8 -48)
  %302 = icmp ult <16 x i8> %301, splat (i8 10)
  %303 = bitcast <16 x i1> %302 to i16
  %304 = and i16 %303, 255
  %305 = icmp eq i16 %304, 255
  br i1 %305, label %326, label %338

306:                                              ; preds = %326
  %307 = getelementptr inbounds nuw i8, ptr %37, i64 %294
  %308 = load i64, ptr %307, align 1
  %309 = insertelement <2 x i64> <i64 poison, i64 0>, i64 %308, i64 0
  %310 = bitcast <2 x i64> %309 to <16 x i8>
  %311 = add <16 x i8> %310, splat (i8 -48)
  %312 = icmp ult <16 x i8> %311, splat (i8 10)
  %313 = bitcast <16 x i1> %312 to i16
  %314 = and i16 %313, 255
  %315 = icmp eq i16 %314, 255
  br i1 %315, label %316, label %338

316:                                              ; preds = %306
  %317 = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %311, <16 x i8> <i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison>)
  %318 = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %317, <8 x i16> <i16 100, i16 1, i16 100, i16 1, i16 poison, i16 poison, i16 poison, i16 poison>)
  %319 = extractelement <4 x i32> %318, i64 0
  %320 = mul i32 %319, 10000
  %321 = extractelement <4 x i32> %318, i64 1
  %322 = add i32 %320, %321
  %323 = mul nuw nsw i64 %335, 100000000
  %324 = zext i32 %322 to i64
  %325 = add nuw nsw i64 %323, %324
  br label %338

326:                                              ; preds = %296
  %327 = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %301, <16 x i8> <i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison>)
  %328 = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %327, <8 x i16> <i16 100, i16 1, i16 100, i16 1, i16 poison, i16 poison, i16 poison, i16 poison>)
  %329 = extractelement <4 x i32> %328, i64 0
  %330 = mul i32 %329, 10000
  %331 = extractelement <4 x i32> %328, i64 1
  %332 = add i32 %330, %331
  %333 = mul nuw nsw i64 %292, 100000000
  %334 = zext i32 %332 to i64
  %335 = add nuw nsw i64 %333, %334
  %336 = or disjoint i64 %293, 16
  %337 = icmp ugt i64 %336, %275
  br i1 %337, label %338, label %306

338:                                              ; preds = %306, %326, %316, %296, %290
  %339 = phi i64 [ %292, %290 ], [ %292, %296 ], [ %335, %326 ], [ %335, %306 ], [ %325, %316 ]
  %340 = phi i64 [ 1, %290 ], [ 1, %296 ], [ 9, %326 ], [ 9, %306 ], [ 17, %316 ]
  %341 = phi i64 [ %293, %290 ], [ %293, %296 ], [ %294, %326 ], [ %294, %306 ], [ %336, %316 ]
  %342 = icmp ult i64 %341, %275
  br i1 %342, label %343, label %363

343:                                              ; preds = %338, %358
  %344 = phi i64 [ %361, %358 ], [ %341, %338 ]
  %345 = phi i64 [ %360, %358 ], [ %340, %338 ]
  %346 = phi i64 [ %359, %358 ], [ %339, %338 ]
  %347 = getelementptr inbounds nuw i8, ptr %37, i64 %344
  %348 = load i8, ptr %347, align 1, !tbaa !12
  %349 = add i8 %348, -48
  %350 = icmp ult i8 %349, 10
  br i1 %350, label %351, label %363

351:                                              ; preds = %343
  %352 = icmp ult i64 %345, 19
  br i1 %352, label %353, label %358

353:                                              ; preds = %351
  %354 = mul i64 %346, 10
  %355 = and i8 %348, 15
  %356 = zext nneg i8 %355 to i64
  %357 = add i64 %354, %356
  br label %358

358:                                              ; preds = %353, %351
  %359 = phi i64 [ %357, %353 ], [ %346, %351 ]
  %360 = add i64 %345, 1
  %361 = add nuw i64 %344, 1
  %362 = icmp ult i64 %361, %275
  br i1 %362, label %343, label %501, !llvm.loop !16

363:                                              ; preds = %343, %338, %285
  %364 = phi i64 [ 0, %285 ], [ %339, %338 ], [ %346, %343 ]
  %365 = phi i64 [ 1, %285 ], [ %340, %338 ], [ %345, %343 ]
  %366 = phi i64 [ %286, %285 ], [ %341, %338 ], [ %344, %343 ]
  %367 = icmp ult i64 %366, %275
  br i1 %367, label %368, label %448

368:                                              ; preds = %363
  %369 = getelementptr inbounds nuw i8, ptr %37, i64 %366
  %370 = load i8, ptr %369, align 1, !tbaa !12
  %371 = icmp eq i8 %370, 46
  br i1 %371, label %372, label %448

372:                                              ; preds = %368
  %373 = add nuw i64 %366, 1
  %374 = icmp ult i64 %373, %275
  br i1 %374, label %375, label %664

375:                                              ; preds = %372
  %376 = getelementptr inbounds nuw i8, ptr %37, i64 %373
  %377 = load i8, ptr %376, align 1, !tbaa !12
  %378 = add i8 %377, -58
  %379 = icmp ult i8 %378, -10
  br i1 %379, label %664, label %380

380:                                              ; preds = %375
  %381 = add i64 %366, 9
  %382 = icmp ugt i64 %381, %275
  br i1 %382, label %423, label %383

383:                                              ; preds = %380
  %384 = getelementptr inbounds nuw i8, ptr %37, i64 %373
  %385 = load i64, ptr %384, align 1
  %386 = insertelement <2 x i64> <i64 poison, i64 0>, i64 %385, i64 0
  %387 = bitcast <2 x i64> %386 to <16 x i8>
  %388 = add <16 x i8> %387, splat (i8 -48)
  %389 = icmp ult <16 x i8> %388, splat (i8 10)
  %390 = bitcast <16 x i1> %389 to i16
  %391 = and i16 %390, 255
  %392 = icmp eq i16 %391, 255
  br i1 %392, label %413, label %423

393:                                              ; preds = %413
  %394 = getelementptr inbounds nuw i8, ptr %37, i64 %381
  %395 = load i64, ptr %394, align 1
  %396 = insertelement <2 x i64> <i64 poison, i64 0>, i64 %395, i64 0
  %397 = bitcast <2 x i64> %396 to <16 x i8>
  %398 = add <16 x i8> %397, splat (i8 -48)
  %399 = icmp ult <16 x i8> %398, splat (i8 10)
  %400 = bitcast <16 x i1> %399 to i16
  %401 = and i16 %400, 255
  %402 = icmp eq i16 %401, 255
  br i1 %402, label %403, label %423

403:                                              ; preds = %393
  %404 = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %398, <16 x i8> <i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison>)
  %405 = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %404, <8 x i16> <i16 100, i16 1, i16 100, i16 1, i16 poison, i16 poison, i16 poison, i16 poison>)
  %406 = extractelement <4 x i32> %405, i64 0
  %407 = mul i32 %406, 10000
  %408 = extractelement <4 x i32> %405, i64 1
  %409 = add i32 %407, %408
  %410 = mul nuw nsw i64 %420, 100000000
  %411 = zext i32 %409 to i64
  %412 = add nuw nsw i64 %410, %411
  br label %423

413:                                              ; preds = %383
  %414 = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %388, <16 x i8> <i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison>)
  %415 = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %414, <8 x i16> <i16 100, i16 1, i16 100, i16 1, i16 poison, i16 poison, i16 poison, i16 poison>)
  %416 = extractelement <4 x i32> %415, i64 0
  %417 = mul i32 %416, 10000
  %418 = extractelement <4 x i32> %415, i64 1
  %419 = add i32 %417, %418
  %420 = zext i32 %419 to i64
  %421 = add i64 %366, 17
  %422 = icmp ugt i64 %421, %275
  br i1 %422, label %423, label %393

423:                                              ; preds = %393, %413, %403, %383, %380
  %424 = phi i64 [ 0, %380 ], [ 0, %383 ], [ %420, %413 ], [ %420, %393 ], [ %412, %403 ]
  %425 = phi i64 [ 0, %380 ], [ 0, %383 ], [ 8, %413 ], [ 8, %393 ], [ 16, %403 ]
  %426 = phi i64 [ %373, %380 ], [ %373, %383 ], [ %381, %413 ], [ %381, %393 ], [ %421, %403 ]
  %427 = icmp ult i64 %426, %275
  br i1 %427, label %428, label %448

428:                                              ; preds = %423, %443
  %429 = phi i64 [ %446, %443 ], [ %426, %423 ]
  %430 = phi i64 [ %445, %443 ], [ %425, %423 ]
  %431 = phi i64 [ %444, %443 ], [ %424, %423 ]
  %432 = getelementptr inbounds nuw i8, ptr %37, i64 %429
  %433 = load i8, ptr %432, align 1, !tbaa !12
  %434 = add i8 %433, -48
  %435 = icmp ult i8 %434, 10
  br i1 %435, label %436, label %448

436:                                              ; preds = %428
  %437 = icmp ult i64 %430, 19
  br i1 %437, label %438, label %443

438:                                              ; preds = %436
  %439 = mul i64 %431, 10
  %440 = and i8 %433, 15
  %441 = zext nneg i8 %440 to i64
  %442 = add i64 %439, %441
  br label %443

443:                                              ; preds = %438, %436
  %444 = phi i64 [ %442, %438 ], [ %431, %436 ]
  %445 = add i64 %430, 1
  %446 = add nuw i64 %429, 1
  %447 = icmp ult i64 %446, %275
  br i1 %447, label %428, label %501, !llvm.loop !17

448:                                              ; preds = %428, %423, %368, %363
  %449 = phi i64 [ 0, %368 ], [ 0, %363 ], [ %424, %423 ], [ %431, %428 ]
  %450 = phi i64 [ 0, %368 ], [ 0, %363 ], [ %425, %423 ], [ %430, %428 ]
  %451 = phi i64 [ %366, %368 ], [ %366, %363 ], [ %426, %423 ], [ %429, %428 ]
  %452 = icmp ult i64 %451, %275
  br i1 %452, label %453, label %497

453:                                              ; preds = %448
  %454 = getelementptr inbounds nuw i8, ptr %37, i64 %451
  %455 = load i8, ptr %454, align 1, !tbaa !12
  switch i8 %455, label %497 [
    i8 101, label %456
    i8 69, label %456
  ]

456:                                              ; preds = %453, %453
  %457 = add nuw i64 %451, 1
  %458 = icmp ult i64 %457, %275
  br i1 %458, label %459, label %465

459:                                              ; preds = %456
  %460 = getelementptr inbounds nuw i8, ptr %37, i64 %457
  %461 = load i8, ptr %460, align 1, !tbaa !12
  switch i8 %461, label %465 [
    i8 43, label %462
    i8 45, label %462
  ]

462:                                              ; preds = %459, %459
  %463 = icmp ne i8 %461, 45
  %464 = add nuw i64 %451, 2
  br label %465

465:                                              ; preds = %462, %459, %456
  %466 = phi i1 [ %463, %462 ], [ true, %456 ], [ true, %459 ]
  %467 = phi i64 [ %464, %462 ], [ %457, %456 ], [ %457, %459 ]
  %468 = icmp ult i64 %467, %275
  br i1 %468, label %469, label %664

469:                                              ; preds = %465
  %470 = getelementptr inbounds nuw i8, ptr %37, i64 %467
  %471 = load i8, ptr %470, align 1, !tbaa !12
  %472 = add i8 %471, -58
  %473 = icmp ult i8 %472, -10
  br i1 %473, label %664, label %474

474:                                              ; preds = %469, %488
  %475 = phi i64 [ %490, %488 ], [ %467, %469 ]
  %476 = phi i64 [ %489, %488 ], [ 0, %469 ]
  %477 = getelementptr inbounds nuw i8, ptr %37, i64 %475
  %478 = load i8, ptr %477, align 1, !tbaa !12
  %479 = add i8 %478, -48
  %480 = icmp ult i8 %479, 10
  br i1 %480, label %481, label %492

481:                                              ; preds = %474
  %482 = icmp slt i64 %476, 100000
  br i1 %482, label %483, label %488

483:                                              ; preds = %481
  %484 = mul i64 %476, 10
  %485 = and i8 %478, 15
  %486 = zext nneg i8 %485 to i64
  %487 = add i64 %484, %486
  br label %488

488:                                              ; preds = %483, %481
  %489 = phi i64 [ %487, %483 ], [ %476, %481 ]
  %490 = add nuw i64 %475, 1
  %491 = icmp ult i64 %490, %275
  br i1 %491, label %474, label %492, !llvm.loop !18

492:                                              ; preds = %474, %488
  %493 = phi i64 [ %476, %474 ], [ %489, %488 ]
  %494 = phi i64 [ %475, %474 ], [ %275, %488 ]
  %495 = sub i64 0, %493
  %496 = select i1 %466, i64 %493, i64 %495
  br label %497

497:                                              ; preds = %492, %453, %448
  %498 = phi i64 [ 0, %448 ], [ 0, %453 ], [ %496, %492 ]
  %499 = phi i64 [ %451, %448 ], [ %451, %453 ], [ %494, %492 ]
  %500 = icmp eq i64 %499, %275
  br i1 %500, label %501, label %664

501:                                              ; preds = %358, %443, %497
  %502 = phi i64 [ %498, %497 ], [ 0, %443 ], [ 0, %358 ]
  %503 = phi i64 [ %365, %497 ], [ %365, %443 ], [ %360, %358 ]
  %504 = phi i64 [ %364, %497 ], [ %364, %443 ], [ %359, %358 ]
  %505 = phi i64 [ %449, %497 ], [ %444, %443 ], [ 0, %358 ]
  %506 = phi i64 [ %450, %497 ], [ %445, %443 ], [ 0, %358 ]
  %507 = sub i64 %502, %506
  %508 = add i64 %506, %503
  %509 = icmp ult i64 %508, 20
  %510 = add i64 %507, 45
  %511 = icmp ult i64 %510, 91
  %512 = select i1 %509, i1 %511, i1 false
  br i1 %512, label %513, label %655

513:                                              ; preds = %501
  %514 = getelementptr inbounds nuw [20 x i64], ptr @NUMF_EL1_P10, i64 0, i64 %506
  %515 = load i64, ptr %514, align 8, !tbaa !6
  %516 = mul i64 %515, %504
  %517 = add i64 %516, %505
  %518 = icmp samesign ult i64 %508, 16
  %519 = add nsw i64 %507, 22
  %520 = icmp ult i64 %519, 45
  %521 = select i1 %518, i1 %520, i1 false
  br i1 %521, label %522, label %538

522:                                              ; preds = %513
  %523 = icmp sgt i64 %507, -1
  %524 = uitofp i64 %517 to double
  br i1 %523, label %525, label %529

525:                                              ; preds = %522
  %526 = getelementptr inbounds nuw [23 x double], ptr @NUMF_EL1_POW10, i64 0, i64 %507
  %527 = load double, ptr %526, align 8, !tbaa !19
  %528 = fmul double %527, %524
  br label %534

529:                                              ; preds = %522
  %530 = sub nsw i64 0, %507
  %531 = getelementptr inbounds nuw [23 x double], ptr @NUMF_EL1_POW10, i64 0, i64 %530
  %532 = load double, ptr %531, align 8, !tbaa !19
  %533 = fdiv double %524, %532
  br label %534

534:                                              ; preds = %529, %525
  %535 = phi double [ %528, %525 ], [ %533, %529 ]
  %536 = fneg double %535
  %537 = select i1 %278, double %536, double %535
  br label %667

538:                                              ; preds = %513
  %539 = icmp eq i64 %517, 0
  br i1 %539, label %645, label %540

540:                                              ; preds = %538
  %541 = getelementptr inbounds nuw [91 x %struct.EPow], ptr @EPOW, i64 0, i64 %510
  %542 = call range(i64 0, 65) i64 @llvm.ctlz.i64(i64 %517, i1 true)
  %543 = trunc nuw nsw i64 %542 to i32
  %544 = shl i64 %517, %542
  %545 = zext i64 %544 to i128
  %546 = load i64, ptr %541, align 8, !tbaa !21
  %547 = zext i64 %546 to i128
  %548 = mul nuw i128 %547, %545
  %549 = lshr i128 %548, 64
  %550 = trunc nuw i128 %549 to i64
  %551 = lshr i64 %550, 63
  %552 = trunc nuw nsw i64 %551 to i32
  %553 = shl nuw nsw i64 %551, 10
  %554 = or disjoint i64 %553, 1023
  %555 = and i64 %554, %550
  %556 = shl nuw nsw i32 512, %552
  %557 = zext nneg i32 %556 to i64
  %558 = sub nsw i64 %555, %557
  %559 = add nsw i64 %558, 2
  %560 = icmp ult i64 %559, 3
  br i1 %560, label %561, label %622, !prof !23

561:                                              ; preds = %540
  %562 = load i64, ptr @g_el_window, align 8, !tbaa !6
  %563 = add i64 %562, 1
  store i64 %563, ptr @g_el_window, align 8, !tbaa !6
  %564 = getelementptr inbounds nuw i8, ptr %541, i64 8
  %565 = load i64, ptr %564, align 8, !tbaa !24
  %566 = zext i64 %565 to i128
  %567 = mul nuw i128 %566, %545
  %568 = trunc i128 %548 to i64
  %569 = trunc i128 %567 to i64
  %570 = lshr i128 %567, 64
  %571 = trunc nuw i128 %570 to i64
  %572 = add i64 %571, %568
  %573 = icmp ult i64 %572, %568
  %574 = zext i1 %573 to i64
  %575 = add nuw i64 %574, %550
  %576 = lshr i64 %575, 63
  %577 = trunc nuw nsw i64 %576 to i32
  %578 = shl nuw nsw i64 %576, 10
  %579 = or disjoint i64 %578, 1023
  %580 = and i64 %579, %575
  %581 = shl nuw nsw i32 512, %577
  %582 = zext nneg i32 %581 to i64
  %583 = icmp eq i64 %580, %582
  %584 = add nsw i64 %582, -1
  %585 = icmp eq i64 %580, %584
  %586 = or i64 %572, %569
  %587 = icmp eq i64 %586, 0
  %588 = and i1 %587, %583
  %589 = icmp eq i64 %572, -1
  %590 = and i1 %589, %585
  %591 = or i1 %588, %590
  %592 = icmp slt i64 %507, 0
  %593 = and i1 %592, %591
  br i1 %593, label %651, label %594, !prof !23

594:                                              ; preds = %561
  %595 = or disjoint i64 %576, 10
  %596 = lshr i64 %575, %595
  %597 = icmp samesign ugt i64 %580, %582
  %598 = icmp ne i64 %586, 0
  %599 = trunc i64 %596 to i1
  %600 = or i1 %598, %599
  %601 = and i1 %583, %600
  %602 = or i1 %597, %601
  %603 = zext i1 %602 to i64
  %604 = add nuw nsw i64 %596, %603
  %605 = lshr i64 %604, 53
  %606 = trunc nuw nsw i64 %605 to i32
  %607 = getelementptr inbounds nuw i8, ptr %541, i64 16
  %608 = load i32, ptr %607, align 8, !tbaa !25
  %609 = sub nsw i32 %577, %543
  %610 = add nsw i32 %609, 190
  %611 = add nuw nsw i32 %610, %606
  %612 = add i32 %611, %608
  %613 = add i32 %612, -1024
  %614 = icmp ult i32 %613, -2046
  br i1 %614, label %651, label %615

615:                                              ; preds = %594
  %616 = add nsw i32 %612, 1023
  %617 = zext nneg i32 %616 to i64
  %618 = shl nuw nsw i64 %617, 52
  %619 = and i64 %604, 4503599627370495
  %620 = or disjoint i64 %618, %619
  %621 = bitcast i64 %620 to double
  br label %645

622:                                              ; preds = %540
  %623 = or disjoint i64 %551, 10
  %624 = lshr i64 %550, %623
  %625 = icmp samesign ugt i64 %555, %557
  %626 = zext i1 %625 to i64
  %627 = add nuw nsw i64 %624, %626
  %628 = lshr i64 %627, 53
  %629 = trunc nuw nsw i64 %628 to i32
  %630 = getelementptr inbounds nuw i8, ptr %541, i64 16
  %631 = load i32, ptr %630, align 8, !tbaa !25
  %632 = sub nsw i32 %552, %543
  %633 = add nsw i32 %632, 190
  %634 = add nuw nsw i32 %633, %629
  %635 = add i32 %634, %631
  %636 = add i32 %635, -1024
  %637 = icmp ult i32 %636, -2046
  br i1 %637, label %651, label %638

638:                                              ; preds = %622
  %639 = add nsw i32 %635, 1023
  %640 = zext nneg i32 %639 to i64
  %641 = shl nuw nsw i64 %640, 52
  %642 = and i64 %627, 4503599627370495
  %643 = or disjoint i64 %641, %642
  %644 = bitcast i64 %643 to double
  br label %645

645:                                              ; preds = %538, %615, %638
  %646 = phi double [ 0.000000e+00, %538 ], [ %621, %615 ], [ %644, %638 ]
  %647 = load i64, ptr @g_nume1_el, align 8, !tbaa !6
  %648 = add i64 %647, 1
  store i64 %648, ptr @g_nume1_el, align 8, !tbaa !6
  %649 = fneg double %646
  %650 = select i1 %278, double %649, double %646
  br label %667

651:                                              ; preds = %622, %594, %561
  %652 = phi ptr [ @g_el_undec, %561 ], [ @g_el_range, %594 ], [ @g_el_range, %622 ]
  %653 = load i64, ptr %652, align 8, !tbaa !6
  %654 = add i64 %653, 1
  store i64 %654, ptr %652, align 8, !tbaa !6
  br label %655

655:                                              ; preds = %651, %501
  call void @llvm.lifetime.start.p0(i64 8, ptr nonnull %16) #11
  %656 = load i64, ptr @g_nume1_slow, align 8, !tbaa !6
  %657 = add i64 %656, 1
  store i64 %657, ptr @g_nume1_slow, align 8, !tbaa !6
  %658 = call fastcc i32 @num_scan(ptr noundef nonnull %37, i64 noundef %275, ptr noundef %16, ptr noundef nonnull %17)
  %659 = icmp eq i32 %658, 0
  br i1 %659, label %660, label %662

660:                                              ; preds = %655
  call void @llvm.lifetime.end.p0(i64 8, ptr nonnull %16) #11
  %661 = load i64, ptr %17, align 8, !tbaa !6
  br label %664

662:                                              ; preds = %655
  %663 = load double, ptr %16, align 8, !tbaa !19
  call void @llvm.lifetime.end.p0(i64 8, ptr nonnull %16) #11
  br label %667

664:                                              ; preds = %497, %469, %465, %372, %375, %287, %274, %660
  %665 = phi i64 [ %661, %660 ], [ %279, %274 ], [ %279, %287 ], [ %373, %375 ], [ %373, %372 ], [ %467, %465 ], [ %467, %469 ], [ %499, %497 ]
  %666 = add i64 %665, %36
  call void @llvm.lifetime.end.p0(i64 8, ptr nonnull %17) #11
  br label %710

667:                                              ; preds = %662, %645, %534
  %668 = phi double [ %663, %662 ], [ %650, %645 ], [ %537, %534 ]
  %669 = add i64 %31, 1
  %670 = icmp ugt i64 %669, %10
  br i1 %670, label %671, label %672

671:                                              ; preds = %667
  call void @llvm.trap()
  unreachable

672:                                              ; preds = %667
  %673 = getelementptr inbounds nuw i8, ptr %9, i64 %31
  store i8 7, ptr %673, align 1
  %674 = add i64 %31, 9
  %675 = icmp ugt i64 %674, %10
  br i1 %675, label %676, label %708

676:                                              ; preds = %672
  call void @llvm.trap()
  unreachable

677:                                              ; preds = %273
  switch i8 %38, label %710 [
    i8 116, label %680
    i8 102, label %678
    i8 110, label %679
  ]

678:                                              ; preds = %677
  br label %680

679:                                              ; preds = %677
  br label %680

680:                                              ; preds = %679, %678, %677
  %681 = phi ptr [ @.str.18, %678 ], [ @.str.19, %679 ], [ @.str.17, %677 ]
  %682 = phi i64 [ 5, %678 ], [ 4, %679 ], [ 4, %677 ]
  %683 = phi i8 [ 9, %678 ], [ 10, %679 ], [ 8, %677 ]
  %684 = sub i64 %248, %36
  %685 = call i64 @llvm.umin.i64(i64 %684, i64 %682)
  %686 = icmp eq i64 %248, %36
  br i1 %686, label %697, label %687

687:                                              ; preds = %680, %694
  %688 = phi i64 [ %695, %694 ], [ 0, %680 ]
  %689 = getelementptr inbounds nuw i8, ptr %37, i64 %688
  %690 = load i8, ptr %689, align 1, !tbaa !12
  %691 = getelementptr inbounds nuw i8, ptr %681, i64 %688
  %692 = load i8, ptr %691, align 1, !tbaa !12
  %693 = icmp eq i8 %690, %692
  br i1 %693, label %694, label %699

694:                                              ; preds = %687
  %695 = add nuw nsw i64 %688, 1
  %696 = icmp eq i64 %695, %685
  br i1 %696, label %697, label %687, !llvm.loop !26

697:                                              ; preds = %694, %680
  %698 = icmp eq i64 %684, %682
  br i1 %698, label %702, label %699

699:                                              ; preds = %697, %687
  %700 = phi i64 [ %688, %687 ], [ %685, %697 ]
  %701 = add i64 %700, %36
  br label %710

702:                                              ; preds = %697
  %703 = add i64 %31, 1
  %704 = icmp ugt i64 %703, %10
  br i1 %704, label %705, label %706

705:                                              ; preds = %702
  call void @llvm.trap()
  unreachable

706:                                              ; preds = %702
  %707 = getelementptr inbounds nuw i8, ptr %9, i64 %31
  store i8 %683, ptr %707, align 1
  br label %1118

708:                                              ; preds = %672
  %709 = getelementptr inbounds nuw i8, ptr %9, i64 %669
  store double %668, ptr %709, align 1
  call void @llvm.lifetime.end.p0(i64 8, ptr nonnull %17) #11
  br label %1118

710:                                              ; preds = %677, %273, %699, %664
  %711 = phi i64 [ %701, %699 ], [ %666, %664 ], [ %36, %273 ], [ %36, %677 ]
  br i1 %228, label %712, label %716

712:                                              ; preds = %710
  %713 = getelementptr inbounds nuw i32, ptr %2, i64 %33
  %714 = load i32, ptr %713, align 4, !tbaa !10
  %715 = zext i32 %714 to i64
  br label %716

716:                                              ; preds = %710, %712
  %717 = phi i64 [ %715, %712 ], [ %1, %710 ]
  %718 = icmp ugt i64 %717, %36
  br i1 %718, label %719, label %726

719:                                              ; preds = %716, %723
  %720 = phi i64 [ %724, %723 ], [ %36, %716 ]
  %721 = getelementptr inbounds nuw i8, ptr %0, i64 %720
  %722 = load i8, ptr %721, align 1, !tbaa !12
  switch i8 %722, label %723 [
    i8 32, label %726
    i8 13, label %726
    i8 10, label %726
    i8 9, label %726
  ]

723:                                              ; preds = %719
  %724 = add i64 %720, 1
  %725 = icmp eq i64 %724, %717
  br i1 %725, label %1162, label %719, !llvm.loop !27

726:                                              ; preds = %719, %719, %719, %719, %716
  %727 = phi i64 [ %36, %716 ], [ %720, %719 ], [ %720, %719 ], [ %720, %719 ], [ %720, %719 ]
  %728 = icmp eq i64 %727, %717
  br i1 %728, label %1162, label %729

729:                                              ; preds = %726
  br i1 %252, label %730, label %1084

730:                                              ; preds = %729
  call void @llvm.lifetime.start.p0(i64 8, ptr nonnull %15) #11
  %731 = sub i64 %727, %36
  %732 = icmp ne i64 %727, %36
  %733 = and i1 %732, %249
  %734 = zext i1 %733 to i64
  %735 = icmp ugt i64 %731, %734
  br i1 %735, label %736, label %1081

736:                                              ; preds = %730
  %737 = getelementptr inbounds nuw i8, ptr %37, i64 %734
  %738 = load i8, ptr %737, align 1, !tbaa !12
  %739 = icmp eq i8 %738, 48
  br i1 %739, label %740, label %742

740:                                              ; preds = %736
  %741 = select i1 %733, i64 2, i64 1
  br label %818

742:                                              ; preds = %736
  %743 = add i8 %738, -49
  %744 = icmp ult i8 %743, 9
  br i1 %744, label %745, label %1081

745:                                              ; preds = %742
  %746 = and i8 %738, 15
  %747 = zext nneg i8 %746 to i64
  %748 = select i1 %733, i64 2, i64 1
  %749 = or disjoint i64 %748, 8
  %750 = icmp ugt i64 %749, %731
  br i1 %750, label %793, label %751

751:                                              ; preds = %745
  %752 = getelementptr inbounds nuw i8, ptr %37, i64 %748
  %753 = load i64, ptr %752, align 1
  %754 = insertelement <2 x i64> <i64 poison, i64 0>, i64 %753, i64 0
  %755 = bitcast <2 x i64> %754 to <16 x i8>
  %756 = add <16 x i8> %755, splat (i8 -48)
  %757 = icmp ult <16 x i8> %756, splat (i8 10)
  %758 = bitcast <16 x i1> %757 to i16
  %759 = and i16 %758, 255
  %760 = icmp eq i16 %759, 255
  br i1 %760, label %781, label %793

761:                                              ; preds = %781
  %762 = getelementptr inbounds nuw i8, ptr %37, i64 %749
  %763 = load i64, ptr %762, align 1
  %764 = insertelement <2 x i64> <i64 poison, i64 0>, i64 %763, i64 0
  %765 = bitcast <2 x i64> %764 to <16 x i8>
  %766 = add <16 x i8> %765, splat (i8 -48)
  %767 = icmp ult <16 x i8> %766, splat (i8 10)
  %768 = bitcast <16 x i1> %767 to i16
  %769 = and i16 %768, 255
  %770 = icmp eq i16 %769, 255
  br i1 %770, label %771, label %793

771:                                              ; preds = %761
  %772 = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %766, <16 x i8> <i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison>)
  %773 = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %772, <8 x i16> <i16 100, i16 1, i16 100, i16 1, i16 poison, i16 poison, i16 poison, i16 poison>)
  %774 = extractelement <4 x i32> %773, i64 0
  %775 = mul i32 %774, 10000
  %776 = extractelement <4 x i32> %773, i64 1
  %777 = add i32 %775, %776
  %778 = mul nuw nsw i64 %790, 100000000
  %779 = zext i32 %777 to i64
  %780 = add nuw nsw i64 %778, %779
  br label %793

781:                                              ; preds = %751
  %782 = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %756, <16 x i8> <i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison>)
  %783 = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %782, <8 x i16> <i16 100, i16 1, i16 100, i16 1, i16 poison, i16 poison, i16 poison, i16 poison>)
  %784 = extractelement <4 x i32> %783, i64 0
  %785 = mul i32 %784, 10000
  %786 = extractelement <4 x i32> %783, i64 1
  %787 = add i32 %785, %786
  %788 = mul nuw nsw i64 %747, 100000000
  %789 = zext i32 %787 to i64
  %790 = add nuw nsw i64 %788, %789
  %791 = or disjoint i64 %748, 16
  %792 = icmp ugt i64 %791, %731
  br i1 %792, label %793, label %761

793:                                              ; preds = %761, %781, %771, %751, %745
  %794 = phi i64 [ %747, %745 ], [ %747, %751 ], [ %790, %781 ], [ %790, %761 ], [ %780, %771 ]
  %795 = phi i64 [ 1, %745 ], [ 1, %751 ], [ 9, %781 ], [ 9, %761 ], [ 17, %771 ]
  %796 = phi i64 [ %748, %745 ], [ %748, %751 ], [ %749, %781 ], [ %749, %761 ], [ %791, %771 ]
  %797 = icmp ult i64 %796, %731
  br i1 %797, label %798, label %818

798:                                              ; preds = %793, %813
  %799 = phi i64 [ %816, %813 ], [ %796, %793 ]
  %800 = phi i64 [ %815, %813 ], [ %795, %793 ]
  %801 = phi i64 [ %814, %813 ], [ %794, %793 ]
  %802 = getelementptr inbounds nuw i8, ptr %37, i64 %799
  %803 = load i8, ptr %802, align 1, !tbaa !12
  %804 = add i8 %803, -48
  %805 = icmp ult i8 %804, 10
  br i1 %805, label %806, label %818

806:                                              ; preds = %798
  %807 = icmp ult i64 %800, 19
  br i1 %807, label %808, label %813

808:                                              ; preds = %806
  %809 = mul i64 %801, 10
  %810 = and i8 %803, 15
  %811 = zext nneg i8 %810 to i64
  %812 = add i64 %809, %811
  br label %813

813:                                              ; preds = %808, %806
  %814 = phi i64 [ %812, %808 ], [ %801, %806 ]
  %815 = add i64 %800, 1
  %816 = add nuw i64 %799, 1
  %817 = icmp ult i64 %816, %731
  br i1 %817, label %798, label %955, !llvm.loop !16

818:                                              ; preds = %798, %793, %740
  %819 = phi i64 [ 0, %740 ], [ %794, %793 ], [ %801, %798 ]
  %820 = phi i64 [ 1, %740 ], [ %795, %793 ], [ %800, %798 ]
  %821 = phi i64 [ %741, %740 ], [ %796, %793 ], [ %799, %798 ]
  %822 = icmp ult i64 %821, %731
  br i1 %822, label %823, label %902

823:                                              ; preds = %818
  %824 = getelementptr inbounds nuw i8, ptr %37, i64 %821
  %825 = load i8, ptr %824, align 1, !tbaa !12
  %826 = icmp eq i8 %825, 46
  br i1 %826, label %827, label %902

827:                                              ; preds = %823
  %828 = add nuw i64 %821, 1
  %829 = icmp ult i64 %828, %731
  br i1 %829, label %830, label %1081

830:                                              ; preds = %827
  %831 = getelementptr inbounds nuw i8, ptr %37, i64 %828
  %832 = load i8, ptr %831, align 1, !tbaa !12
  %833 = add i8 %832, -58
  %834 = icmp ult i8 %833, -10
  br i1 %834, label %1081, label %835

835:                                              ; preds = %830
  %836 = add i64 %821, 9
  %837 = icmp ugt i64 %836, %731
  br i1 %837, label %877, label %838

838:                                              ; preds = %835
  %839 = load i64, ptr %831, align 1
  %840 = insertelement <2 x i64> <i64 poison, i64 0>, i64 %839, i64 0
  %841 = bitcast <2 x i64> %840 to <16 x i8>
  %842 = add <16 x i8> %841, splat (i8 -48)
  %843 = icmp ult <16 x i8> %842, splat (i8 10)
  %844 = bitcast <16 x i1> %843 to i16
  %845 = and i16 %844, 255
  %846 = icmp eq i16 %845, 255
  br i1 %846, label %867, label %877

847:                                              ; preds = %867
  %848 = getelementptr inbounds nuw i8, ptr %37, i64 %836
  %849 = load i64, ptr %848, align 1
  %850 = insertelement <2 x i64> <i64 poison, i64 0>, i64 %849, i64 0
  %851 = bitcast <2 x i64> %850 to <16 x i8>
  %852 = add <16 x i8> %851, splat (i8 -48)
  %853 = icmp ult <16 x i8> %852, splat (i8 10)
  %854 = bitcast <16 x i1> %853 to i16
  %855 = and i16 %854, 255
  %856 = icmp eq i16 %855, 255
  br i1 %856, label %857, label %877

857:                                              ; preds = %847
  %858 = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %852, <16 x i8> <i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison>)
  %859 = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %858, <8 x i16> <i16 100, i16 1, i16 100, i16 1, i16 poison, i16 poison, i16 poison, i16 poison>)
  %860 = extractelement <4 x i32> %859, i64 0
  %861 = mul i32 %860, 10000
  %862 = extractelement <4 x i32> %859, i64 1
  %863 = add i32 %861, %862
  %864 = mul nuw nsw i64 %874, 100000000
  %865 = zext i32 %863 to i64
  %866 = add nuw nsw i64 %864, %865
  br label %877

867:                                              ; preds = %838
  %868 = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %842, <16 x i8> <i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 10, i8 1, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison, i8 poison>)
  %869 = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %868, <8 x i16> <i16 100, i16 1, i16 100, i16 1, i16 poison, i16 poison, i16 poison, i16 poison>)
  %870 = extractelement <4 x i32> %869, i64 0
  %871 = mul i32 %870, 10000
  %872 = extractelement <4 x i32> %869, i64 1
  %873 = add i32 %871, %872
  %874 = zext i32 %873 to i64
  %875 = add i64 %821, 17
  %876 = icmp ugt i64 %875, %731
  br i1 %876, label %877, label %847

877:                                              ; preds = %847, %867, %857, %838, %835
  %878 = phi i64 [ 0, %835 ], [ 0, %838 ], [ %874, %867 ], [ %874, %847 ], [ %866, %857 ]
  %879 = phi i64 [ 0, %835 ], [ 0, %838 ], [ 8, %867 ], [ 8, %847 ], [ 16, %857 ]
  %880 = phi i64 [ %828, %835 ], [ %828, %838 ], [ %836, %867 ], [ %836, %847 ], [ %875, %857 ]
  %881 = icmp ult i64 %880, %731
  br i1 %881, label %882, label %902

882:                                              ; preds = %877, %897
  %883 = phi i64 [ %900, %897 ], [ %880, %877 ]
  %884 = phi i64 [ %899, %897 ], [ %879, %877 ]
  %885 = phi i64 [ %898, %897 ], [ %878, %877 ]
  %886 = getelementptr inbounds nuw i8, ptr %37, i64 %883
  %887 = load i8, ptr %886, align 1, !tbaa !12
  %888 = add i8 %887, -48
  %889 = icmp ult i8 %888, 10
  br i1 %889, label %890, label %902

890:                                              ; preds = %882
  %891 = icmp ult i64 %884, 19
  br i1 %891, label %892, label %897

892:                                              ; preds = %890
  %893 = mul i64 %885, 10
  %894 = and i8 %887, 15
  %895 = zext nneg i8 %894 to i64
  %896 = add i64 %893, %895
  br label %897

897:                                              ; preds = %892, %890
  %898 = phi i64 [ %896, %892 ], [ %885, %890 ]
  %899 = add i64 %884, 1
  %900 = add nuw i64 %883, 1
  %901 = icmp ult i64 %900, %731
  br i1 %901, label %882, label %955, !llvm.loop !17

902:                                              ; preds = %882, %877, %823, %818
  %903 = phi i64 [ 0, %823 ], [ 0, %818 ], [ %878, %877 ], [ %885, %882 ]
  %904 = phi i64 [ 0, %823 ], [ 0, %818 ], [ %879, %877 ], [ %884, %882 ]
  %905 = phi i64 [ %821, %823 ], [ %821, %818 ], [ %880, %877 ], [ %883, %882 ]
  %906 = icmp ult i64 %905, %731
  br i1 %906, label %907, label %951

907:                                              ; preds = %902
  %908 = getelementptr inbounds nuw i8, ptr %37, i64 %905
  %909 = load i8, ptr %908, align 1, !tbaa !12
  switch i8 %909, label %951 [
    i8 101, label %910
    i8 69, label %910
  ]

910:                                              ; preds = %907, %907
  %911 = add nuw i64 %905, 1
  %912 = icmp ult i64 %911, %731
  br i1 %912, label %913, label %919

913:                                              ; preds = %910
  %914 = getelementptr inbounds nuw i8, ptr %37, i64 %911
  %915 = load i8, ptr %914, align 1, !tbaa !12
  switch i8 %915, label %919 [
    i8 43, label %916
    i8 45, label %916
  ]

916:                                              ; preds = %913, %913
  %917 = icmp ne i8 %915, 45
  %918 = add nuw i64 %905, 2
  br label %919

919:                                              ; preds = %916, %913, %910
  %920 = phi i1 [ %917, %916 ], [ true, %910 ], [ true, %913 ]
  %921 = phi i64 [ %918, %916 ], [ %911, %910 ], [ %911, %913 ]
  %922 = icmp ult i64 %921, %731
  br i1 %922, label %923, label %1081

923:                                              ; preds = %919
  %924 = getelementptr inbounds nuw i8, ptr %37, i64 %921
  %925 = load i8, ptr %924, align 1, !tbaa !12
  %926 = add i8 %925, -58
  %927 = icmp ult i8 %926, -10
  br i1 %927, label %1081, label %928

928:                                              ; preds = %923, %942
  %929 = phi i64 [ %944, %942 ], [ %921, %923 ]
  %930 = phi i64 [ %943, %942 ], [ 0, %923 ]
  %931 = getelementptr inbounds nuw i8, ptr %37, i64 %929
  %932 = load i8, ptr %931, align 1, !tbaa !12
  %933 = add i8 %932, -48
  %934 = icmp ult i8 %933, 10
  br i1 %934, label %935, label %946

935:                                              ; preds = %928
  %936 = icmp slt i64 %930, 100000
  br i1 %936, label %937, label %942

937:                                              ; preds = %935
  %938 = mul i64 %930, 10
  %939 = and i8 %932, 15
  %940 = zext nneg i8 %939 to i64
  %941 = add i64 %938, %940
  br label %942

942:                                              ; preds = %937, %935
  %943 = phi i64 [ %941, %937 ], [ %930, %935 ]
  %944 = add nuw i64 %929, 1
  %945 = icmp ult i64 %944, %731
  br i1 %945, label %928, label %946, !llvm.loop !18

946:                                              ; preds = %942, %928
  %947 = phi i64 [ %930, %928 ], [ %943, %942 ]
  %948 = phi i64 [ %929, %928 ], [ %731, %942 ]
  %949 = sub i64 0, %947
  %950 = select i1 %920, i64 %947, i64 %949
  br label %951

951:                                              ; preds = %946, %907, %902
  %952 = phi i64 [ 0, %902 ], [ 0, %907 ], [ %950, %946 ]
  %953 = phi i64 [ %905, %902 ], [ %905, %907 ], [ %948, %946 ]
  %954 = icmp eq i64 %953, %731
  br i1 %954, label %955, label %1081

955:                                              ; preds = %813, %897, %951
  %956 = phi i64 [ %952, %951 ], [ 0, %897 ], [ 0, %813 ]
  %957 = phi i64 [ %820, %951 ], [ %820, %897 ], [ %815, %813 ]
  %958 = phi i64 [ %819, %951 ], [ %819, %897 ], [ %814, %813 ]
  %959 = phi i64 [ %903, %951 ], [ %898, %897 ], [ 0, %813 ]
  %960 = phi i64 [ %904, %951 ], [ %899, %897 ], [ 0, %813 ]
  %961 = sub i64 %956, %960
  %962 = add i64 %960, %957
  %963 = icmp ult i64 %962, 20
  %964 = add i64 %961, 45
  %965 = icmp ult i64 %964, 91
  %966 = select i1 %963, i1 %965, i1 false
  br i1 %966, label %967, label %1074

967:                                              ; preds = %955
  %968 = getelementptr inbounds nuw [20 x i64], ptr @NUMF_EL1_P10, i64 0, i64 %960
  %969 = load i64, ptr %968, align 8, !tbaa !6
  %970 = mul i64 %969, %958
  %971 = add i64 %970, %959
  %972 = icmp samesign ult i64 %962, 16
  %973 = add nsw i64 %961, 22
  %974 = icmp ult i64 %973, 45
  %975 = select i1 %972, i1 %974, i1 false
  br i1 %975, label %1108, label %976

976:                                              ; preds = %967
  %977 = icmp eq i64 %971, 0
  br i1 %977, label %1067, label %978

978:                                              ; preds = %976
  %979 = getelementptr inbounds nuw [91 x %struct.EPow], ptr @EPOW, i64 0, i64 %964
  %980 = call range(i64 0, 65) i64 @llvm.ctlz.i64(i64 %971, i1 true)
  %981 = trunc nuw nsw i64 %980 to i32
  %982 = shl i64 %971, %980
  %983 = zext i64 %982 to i128
  %984 = load i64, ptr %979, align 8, !tbaa !21
  %985 = zext i64 %984 to i128
  %986 = mul nuw i128 %985, %983
  %987 = lshr i128 %986, 64
  %988 = trunc nuw i128 %987 to i64
  %989 = lshr i64 %988, 63
  %990 = trunc nuw nsw i64 %989 to i32
  %991 = shl nuw nsw i64 %989, 10
  %992 = or disjoint i64 %991, 1023
  %993 = and i64 %992, %988
  %994 = shl nuw nsw i32 512, %990
  %995 = zext nneg i32 %994 to i64
  %996 = sub nsw i64 %993, %995
  %997 = add nsw i64 %996, 2
  %998 = icmp ult i64 %997, 3
  br i1 %998, label %999, label %1052, !prof !23

999:                                              ; preds = %978
  %1000 = load i64, ptr @g_el_window, align 8, !tbaa !6
  %1001 = add i64 %1000, 1
  store i64 %1001, ptr @g_el_window, align 8, !tbaa !6
  %1002 = getelementptr inbounds nuw i8, ptr %979, i64 8
  %1003 = load i64, ptr %1002, align 8, !tbaa !24
  %1004 = zext i64 %1003 to i128
  %1005 = mul nuw i128 %1004, %983
  %1006 = trunc i128 %986 to i64
  %1007 = trunc i128 %1005 to i64
  %1008 = lshr i128 %1005, 64
  %1009 = trunc nuw i128 %1008 to i64
  %1010 = add i64 %1009, %1006
  %1011 = icmp ult i64 %1010, %1006
  %1012 = zext i1 %1011 to i64
  %1013 = add nuw i64 %1012, %988
  %1014 = lshr i64 %1013, 63
  %1015 = trunc nuw nsw i64 %1014 to i32
  %1016 = shl nuw nsw i64 %1014, 10
  %1017 = or disjoint i64 %1016, 1023
  %1018 = and i64 %1017, %1013
  %1019 = shl nuw nsw i32 512, %1015
  %1020 = zext nneg i32 %1019 to i64
  %1021 = icmp eq i64 %1018, %1020
  %1022 = add nsw i64 %1020, -1
  %1023 = icmp eq i64 %1018, %1022
  %1024 = or i64 %1010, %1007
  %1025 = icmp eq i64 %1024, 0
  %1026 = and i1 %1025, %1021
  %1027 = icmp eq i64 %1010, -1
  %1028 = and i1 %1027, %1023
  %1029 = or i1 %1026, %1028
  %1030 = icmp slt i64 %961, 0
  %1031 = and i1 %1030, %1029
  br i1 %1031, label %1070, label %1032, !prof !23

1032:                                             ; preds = %999
  %1033 = or disjoint i64 %1014, 10
  %1034 = lshr i64 %1013, %1033
  %1035 = icmp samesign ugt i64 %1018, %1020
  %1036 = icmp ne i64 %1024, 0
  %1037 = trunc i64 %1034 to i1
  %1038 = or i1 %1036, %1037
  %1039 = and i1 %1021, %1038
  %1040 = or i1 %1035, %1039
  %1041 = zext i1 %1040 to i64
  %1042 = add nuw nsw i64 %1034, %1041
  %1043 = lshr i64 %1042, 53
  %1044 = trunc nuw nsw i64 %1043 to i32
  %1045 = getelementptr inbounds nuw i8, ptr %979, i64 16
  %1046 = load i32, ptr %1045, align 8, !tbaa !25
  %1047 = sub nsw i32 %1015, %981
  %1048 = add nsw i32 %1047, -834
  %1049 = add nuw nsw i32 %1048, %1044
  %1050 = add i32 %1049, %1046
  %1051 = icmp ult i32 %1050, -2046
  br i1 %1051, label %1070, label %1067

1052:                                             ; preds = %978
  %1053 = or disjoint i64 %989, 10
  %1054 = lshr i64 %988, %1053
  %1055 = icmp samesign ugt i64 %993, %995
  %1056 = zext i1 %1055 to i64
  %1057 = add nuw nsw i64 %1054, %1056
  %1058 = lshr i64 %1057, 53
  %1059 = trunc nuw nsw i64 %1058 to i32
  %1060 = getelementptr inbounds nuw i8, ptr %979, i64 16
  %1061 = load i32, ptr %1060, align 8, !tbaa !25
  %1062 = sub nsw i32 %990, %981
  %1063 = add nsw i32 %1062, -834
  %1064 = add nuw nsw i32 %1063, %1059
  %1065 = add i32 %1064, %1061
  %1066 = icmp ult i32 %1065, -2046
  br i1 %1066, label %1070, label %1067

1067:                                             ; preds = %1052, %1032, %976
  %1068 = load i64, ptr @g_nume1_el, align 8, !tbaa !6
  %1069 = add i64 %1068, 1
  store i64 %1069, ptr @g_nume1_el, align 8, !tbaa !6
  br label %1108

1070:                                             ; preds = %1052, %1032, %999
  %1071 = phi ptr [ @g_el_undec, %999 ], [ @g_el_range, %1032 ], [ @g_el_range, %1052 ]
  %1072 = load i64, ptr %1071, align 8, !tbaa !6
  %1073 = add i64 %1072, 1
  store i64 %1073, ptr %1071, align 8, !tbaa !6
  br label %1074

1074:                                             ; preds = %1070, %955
  call void @llvm.lifetime.start.p0(i64 8, ptr nonnull %14) #11
  %1075 = load i64, ptr @g_nume1_slow, align 8, !tbaa !6
  %1076 = add i64 %1075, 1
  store i64 %1076, ptr @g_nume1_slow, align 8, !tbaa !6
  %1077 = call fastcc i32 @num_scan(ptr noundef nonnull %37, i64 noundef %731, ptr noundef %14, ptr noundef nonnull %15)
  %1078 = icmp eq i32 %1077, 0
  call void @llvm.lifetime.end.p0(i64 8, ptr nonnull %14) #11
  br i1 %1078, label %1079, label %1108

1079:                                             ; preds = %1074
  %1080 = load i64, ptr %15, align 8, !tbaa !6
  br label %1081

1081:                                             ; preds = %1079, %951, %923, %919, %830, %827, %742, %730
  %1082 = phi i64 [ %1080, %1079 ], [ %734, %730 ], [ %734, %742 ], [ %828, %830 ], [ %828, %827 ], [ %921, %919 ], [ %921, %923 ], [ %953, %951 ]
  %1083 = add i64 %1082, %36
  call void @llvm.lifetime.end.p0(i64 8, ptr nonnull %15) #11
  br label %1162

1084:                                             ; preds = %729
  switch i8 %38, label %1162 [
    i8 116, label %1087
    i8 102, label %1085
    i8 110, label %1086
  ]

1085:                                             ; preds = %1084
  br label %1087

1086:                                             ; preds = %1084
  br label %1087

1087:                                             ; preds = %1086, %1085, %1084
  %1088 = phi ptr [ @.str.18, %1085 ], [ @.str.19, %1086 ], [ @.str.17, %1084 ]
  %1089 = phi i64 [ 5, %1085 ], [ 4, %1086 ], [ 4, %1084 ]
  %1090 = sub i64 %727, %36
  %1091 = call i64 @llvm.umin.i64(i64 %1090, i64 %1089)
  %1092 = icmp eq i64 %727, %36
  br i1 %1092, label %1103, label %1093

1093:                                             ; preds = %1087, %1100
  %1094 = phi i64 [ %1101, %1100 ], [ 0, %1087 ]
  %1095 = getelementptr inbounds nuw i8, ptr %37, i64 %1094
  %1096 = load i8, ptr %1095, align 1, !tbaa !12
  %1097 = getelementptr inbounds nuw i8, ptr %1088, i64 %1094
  %1098 = load i8, ptr %1097, align 1, !tbaa !12
  %1099 = icmp eq i8 %1096, %1098
  br i1 %1099, label %1100, label %1105

1100:                                             ; preds = %1093
  %1101 = add nuw nsw i64 %1094, 1
  %1102 = icmp eq i64 %1101, %1091
  br i1 %1102, label %1103, label %1093, !llvm.loop !26

1103:                                             ; preds = %1100, %1087
  %1104 = icmp eq i64 %1090, %1089
  br i1 %1104, label %1109, label %1105

1105:                                             ; preds = %1093, %1103
  %1106 = phi i64 [ %1091, %1103 ], [ %1094, %1093 ]
  %1107 = add i64 %1106, %36
  br label %1162

1108:                                             ; preds = %1074, %1067, %967
  call void @llvm.lifetime.end.p0(i64 8, ptr nonnull %15) #11
  br label %1109

1109:                                             ; preds = %1108, %1103
  %1110 = icmp ult i64 %727, %717
  br i1 %1110, label %1111, label %1162

1111:                                             ; preds = %1109, %1115
  %1112 = phi i64 [ %1116, %1115 ], [ %727, %1109 ]
  %1113 = getelementptr inbounds nuw i8, ptr %0, i64 %1112
  %1114 = load i8, ptr %1113, align 1, !tbaa !12
  switch i8 %1114, label %1162 [
    i8 32, label %1115
    i8 13, label %1115
    i8 10, label %1115
    i8 9, label %1115
  ]

1115:                                             ; preds = %1111, %1111, %1111, %1111
  %1116 = add i64 %1112, 1
  %1117 = icmp eq i64 %1116, %717
  br i1 %1117, label %1162, label %1111, !llvm.loop !28

1118:                                             ; preds = %708, %706
  %1119 = phi i64 [ %674, %708 ], [ %703, %706 ]
  br i1 %259, label %1128, label %1120

1120:                                             ; preds = %1118
  %1121 = add i32 %28, -1
  %1122 = zext i32 %1121 to i64
  %1123 = getelementptr inbounds nuw i8, ptr %19, i64 %1122
  %1124 = load i8, ptr %1123, align 1, !tbaa !12
  %1125 = icmp eq i8 %1124, 1
  %1126 = select i1 %1125, i8 3, i8 1
  %1127 = getelementptr inbounds nuw i8, ptr %20, i64 %1122
  store i8 %1126, ptr %1127, align 1, !tbaa !12
  br label %1128

1128:                                             ; preds = %1118, %1120
  %1129 = phi i32 [ %29, %1120 ], [ 1, %1118 ]
  %1130 = icmp ult i64 %248, %234
  br i1 %1130, label %1131, label %1138

1131:                                             ; preds = %1128, %1135
  %1132 = phi i64 [ %1136, %1135 ], [ %248, %1128 ]
  %1133 = getelementptr inbounds nuw i8, ptr %0, i64 %1132
  %1134 = load i8, ptr %1133, align 1, !tbaa !12
  switch i8 %1134, label %1162 [
    i8 32, label %1135
    i8 13, label %1135
    i8 10, label %1135
    i8 9, label %1135
  ]

1135:                                             ; preds = %1131, %1131, %1131, %1131
  %1136 = add i64 %1132, 1
  %1137 = icmp eq i64 %1136, %234
  br i1 %1137, label %1138, label %1131, !llvm.loop !29

1138:                                             ; preds = %1135, %1128, %211, %216, %134, %121, %118, %103, %67
  %1139 = phi i64 [ %64, %67 ], [ %100, %103 ], [ %32, %118 ], [ %32, %121 ], [ %32, %134 ], [ %202, %211 ], [ %202, %216 ], [ %1119, %1128 ], [ %1119, %1135 ]
  %1140 = phi i64 [ %64, %67 ], [ %100, %103 ], [ %31, %118 ], [ %31, %121 ], [ %31, %134 ], [ %202, %211 ], [ %202, %216 ], [ %1119, %1128 ], [ %1119, %1135 ]
  %1141 = phi i64 [ %30, %67 ], [ %30, %103 ], [ %30, %118 ], [ %30, %121 ], [ %30, %134 ], [ %201, %211 ], [ %201, %216 ], [ %30, %1128 ], [ %30, %1135 ]
  %1142 = phi i32 [ %29, %67 ], [ %99, %103 ], [ %29, %118 ], [ %29, %121 ], [ %29, %134 ], [ %29, %211 ], [ %29, %216 ], [ %1129, %1128 ], [ %1129, %1135 ]
  %1143 = phi i32 [ %69, %67 ], [ %74, %103 ], [ %28, %118 ], [ %28, %121 ], [ %28, %134 ], [ %28, %211 ], [ %28, %216 ], [ %28, %1128 ], [ %28, %1135 ]
  %1144 = phi i64 [ %33, %67 ], [ %33, %103 ], [ %33, %118 ], [ %33, %121 ], [ %33, %134 ], [ %138, %211 ], [ %138, %216 ], [ %33, %1128 ], [ %33, %1135 ]
  %1145 = icmp ult i64 %1144, %3
  br i1 %1145, label %1146, label %1155

1146:                                             ; preds = %1138, %1153
  %1147 = phi i64 [ %1144, %1138 ], [ %138, %1153 ]
  %1148 = phi i32 [ %1143, %1138 ], [ 0, %1153 ]
  %1149 = phi i32 [ %1142, %1138 ], [ 1, %1153 ]
  %1150 = phi i64 [ %1141, %1138 ], [ %201, %1153 ]
  %1151 = phi i64 [ %1140, %1138 ], [ %202, %1153 ]
  %1152 = phi i64 [ %1139, %1138 ], [ %202, %1153 ]
  br label %26, !llvm.loop !30

1153:                                             ; preds = %215
  %1154 = icmp ult i64 %138, %3
  br i1 %1154, label %1146, label %1159

1155:                                             ; preds = %1138
  %1156 = icmp ne i32 %1143, 0
  %1157 = icmp eq i32 %1142, 0
  %1158 = select i1 %1156, i1 true, i1 %1157
  br i1 %1158, label %1162, label %1159

1159:                                             ; preds = %1153, %1155
  %1160 = phi i64 [ %1139, %1155 ], [ %202, %1153 ]
  %1161 = phi i64 [ %1141, %1155 ], [ %201, %1153 ]
  call void @llvm.lifetime.end.p0(i64 8, ptr nonnull %21) #11
  call void @llvm.lifetime.end.p0(i64 520, ptr nonnull %20) #11
  call void @llvm.lifetime.end.p0(i64 520, ptr nonnull %19) #11
  store i64 %1161, ptr %8, align 8, !tbaa !6
  store i64 %1160, ptr %11, align 8, !tbaa !6
  br label %1166

1162:                                             ; preds = %260, %270, %162, %137, %135, %124, %130, %122, %119, %116, %106, %86, %85, %73, %71, %56, %41, %51, %55, %272, %1131, %723, %1111, %1115, %1155, %13, %1109, %1084, %726, %1081, %1105, %224
  %1163 = phi i64 [ %711, %726 ], [ %1083, %1081 ], [ %1107, %1105 ], [ %226, %224 ], [ %36, %1084 ], [ %727, %1109 ], [ %1, %1155 ], [ %1, %13 ], [ %717, %1115 ], [ %1112, %1111 ], [ %711, %723 ], [ %1132, %1131 ], [ %36, %272 ], [ %36, %55 ], [ %36, %51 ], [ %36, %41 ], [ %36, %56 ], [ %36, %71 ], [ %36, %73 ], [ %36, %85 ], [ %36, %86 ], [ %36, %106 ], [ %36, %116 ], [ %36, %119 ], [ %36, %122 ], [ %36, %130 ], [ %36, %124 ], [ %36, %135 ], [ %36, %137 ], [ %36, %162 ], [ %36, %270 ], [ %36, %260 ]
  %1164 = phi i64 [ %32, %726 ], [ %32, %1081 ], [ %32, %1105 ], [ %32, %224 ], [ %32, %1084 ], [ %32, %1109 ], [ %1139, %1155 ], [ %23, %13 ], [ %32, %1115 ], [ %32, %1111 ], [ %32, %723 ], [ %1119, %1131 ], [ %32, %272 ], [ %32, %55 ], [ %32, %51 ], [ %32, %41 ], [ %32, %56 ], [ %32, %71 ], [ %32, %73 ], [ %32, %85 ], [ %32, %86 ], [ %32, %106 ], [ %32, %116 ], [ %32, %119 ], [ %32, %122 ], [ %32, %130 ], [ %32, %124 ], [ %32, %135 ], [ %32, %137 ], [ %32, %162 ], [ %32, %270 ], [ %32, %260 ]
  %1165 = phi i64 [ %30, %726 ], [ %30, %1081 ], [ %30, %1105 ], [ %30, %224 ], [ %30, %1084 ], [ %30, %1109 ], [ %1141, %1155 ], [ %22, %13 ], [ %30, %1115 ], [ %30, %1111 ], [ %30, %723 ], [ %30, %1131 ], [ %30, %272 ], [ %30, %55 ], [ %30, %51 ], [ %30, %41 ], [ %30, %56 ], [ %30, %71 ], [ %30, %73 ], [ %30, %85 ], [ %30, %86 ], [ %30, %106 ], [ %30, %116 ], [ %30, %119 ], [ %30, %122 ], [ %30, %130 ], [ %30, %124 ], [ %30, %135 ], [ %30, %137 ], [ %30, %162 ], [ %30, %270 ], [ %30, %260 ]
  call void @llvm.lifetime.end.p0(i64 8, ptr nonnull %21) #11
  call void @llvm.lifetime.end.p0(i64 520, ptr nonnull %20) #11
  call void @llvm.lifetime.end.p0(i64 520, ptr nonnull %19) #11
  store i64 %1165, ptr %8, align 8, !tbaa !6
  store i64 %1164, ptr %11, align 8, !tbaa !6
  store i64 %1163, ptr %12, align 8, !tbaa !6
  br label %1166

1166:                                             ; preds = %1159, %1162
  %1167 = phi i64 [ 0, %1162 ], [ 1, %1159 ]
  ret i64 %1167
}

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(i64 immarg, ptr captures(none)) #1

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(i64 immarg, ptr captures(none)) #1

; Function Attrs: cold noreturn nounwind memory(inaccessiblemem: write)
declare void @llvm.trap() #2

declare i64 @leanllvm_json_escape_expand(ptr noundef, i64 noundef, ptr noundef, ptr noundef, ptr noundef, ptr noundef, i64 noundef, i64 noundef) local_unnamed_addr #3

; Function Attrs: nocallback nofree nounwind memory(argmem: readwrite)
declare ptr @__memcpy_chk(ptr noalias noundef writeonly, ptr noalias noundef readonly captures(none), i64 noundef, i64 noundef) local_unnamed_addr #4

; Function Attrs: nofree norecurse nounwind sspstrong memory(argmem: readwrite) uwtable
define internal fastcc range(i32 0, 2) i32 @num_scan(ptr noundef readonly captures(none) %0, i64 noundef range(i64 1, 0) %1, ptr noundef nonnull writeonly captures(none) %2, ptr noundef nonnull writeonly captures(none) %3) unnamed_addr #5 align 64 {
  %5 = alloca [768 x i8], align 16
  %6 = alloca %struct.Stk, align 8
  %7 = load i8, ptr %0, align 1, !tbaa !12
  %8 = icmp eq i8 %7, 45
  %9 = zext i1 %8 to i64
  %10 = icmp ugt i64 %1, %9
  br i1 %10, label %12, label %11

11:                                               ; preds = %4
  store i64 1, ptr %3, align 8, !tbaa !6
  br label %1033

12:                                               ; preds = %4
  %13 = getelementptr inbounds nuw i8, ptr %0, i64 %9
  %14 = load i8, ptr %13, align 1, !tbaa !12
  %15 = icmp eq i8 %14, 48
  br i1 %15, label %16, label %18

16:                                               ; preds = %12
  %17 = select i1 %8, i64 2, i64 1
  br label %31

18:                                               ; preds = %12
  %19 = add i8 %14, -49
  %20 = icmp ult i8 %19, 9
  br i1 %20, label %21, label %30

21:                                               ; preds = %18, %27
  %22 = phi i64 [ %28, %27 ], [ %9, %18 ]
  %23 = getelementptr inbounds nuw i8, ptr %0, i64 %22
  %24 = load i8, ptr %23, align 1, !tbaa !12
  %25 = add i8 %24, -48
  %26 = icmp ult i8 %25, 10
  br i1 %26, label %27, label %31

27:                                               ; preds = %21
  %28 = add i64 %22, 1
  %29 = icmp eq i64 %28, %1
  br i1 %29, label %92, label %21, !llvm.loop !31

30:                                               ; preds = %18
  store i64 %9, ptr %3, align 8, !tbaa !6
  br label %1033

31:                                               ; preds = %21, %16
  %32 = phi i64 [ %17, %16 ], [ %22, %21 ]
  %33 = icmp ult i64 %32, %1
  br i1 %33, label %34, label %56

34:                                               ; preds = %31
  %35 = getelementptr inbounds nuw i8, ptr %0, i64 %32
  %36 = load i8, ptr %35, align 1, !tbaa !12
  %37 = icmp eq i8 %36, 46
  br i1 %37, label %38, label %56

38:                                               ; preds = %34
  %39 = add nuw i64 %32, 1
  %40 = icmp ult i64 %39, %1
  br i1 %40, label %41, label %46

41:                                               ; preds = %38
  %42 = getelementptr inbounds nuw i8, ptr %0, i64 %39
  %43 = load i8, ptr %42, align 1, !tbaa !12
  %44 = add i8 %43, -58
  %45 = icmp ult i8 %44, -10
  br i1 %45, label %46, label %47

46:                                               ; preds = %41, %38
  store i64 %39, ptr %3, align 8, !tbaa !6
  br label %1033

47:                                               ; preds = %41, %53
  %48 = phi i64 [ %54, %53 ], [ %39, %41 ]
  %49 = getelementptr inbounds nuw i8, ptr %0, i64 %48
  %50 = load i8, ptr %49, align 1, !tbaa !12
  %51 = add i8 %50, -48
  %52 = icmp ult i8 %51, 10
  br i1 %52, label %53, label %56

53:                                               ; preds = %47
  %54 = add i64 %48, 1
  %55 = icmp eq i64 %54, %1
  br i1 %55, label %92, label %47, !llvm.loop !32

56:                                               ; preds = %47, %34, %31
  %57 = phi i64 [ %32, %34 ], [ %32, %31 ], [ %48, %47 ]
  %58 = icmp ult i64 %57, %1
  br i1 %58, label %59, label %88

59:                                               ; preds = %56
  %60 = getelementptr inbounds nuw i8, ptr %0, i64 %57
  %61 = load i8, ptr %60, align 1, !tbaa !12
  switch i8 %61, label %88 [
    i8 101, label %62
    i8 69, label %62
  ]

62:                                               ; preds = %59, %59
  %63 = add nuw i64 %57, 1
  %64 = icmp ult i64 %63, %1
  br i1 %64, label %65, label %70

65:                                               ; preds = %62
  %66 = getelementptr inbounds nuw i8, ptr %0, i64 %63
  %67 = load i8, ptr %66, align 1, !tbaa !12
  switch i8 %67, label %70 [
    i8 43, label %68
    i8 45, label %68
  ]

68:                                               ; preds = %65, %65
  %69 = add nuw i64 %57, 2
  br label %70

70:                                               ; preds = %65, %68, %62
  %71 = phi i64 [ %69, %68 ], [ %63, %62 ], [ %63, %65 ]
  %72 = icmp ult i64 %71, %1
  br i1 %72, label %73, label %78

73:                                               ; preds = %70
  %74 = getelementptr inbounds nuw i8, ptr %0, i64 %71
  %75 = load i8, ptr %74, align 1, !tbaa !12
  %76 = add i8 %75, -58
  %77 = icmp ult i8 %76, -10
  br i1 %77, label %78, label %79

78:                                               ; preds = %73, %70
  store i64 %71, ptr %3, align 8, !tbaa !6
  br label %1033

79:                                               ; preds = %73, %85
  %80 = phi i64 [ %86, %85 ], [ %71, %73 ]
  %81 = getelementptr inbounds nuw i8, ptr %0, i64 %80
  %82 = load i8, ptr %81, align 1, !tbaa !12
  %83 = add i8 %82, -48
  %84 = icmp ult i8 %83, 10
  br i1 %84, label %85, label %88

85:                                               ; preds = %79
  %86 = add i64 %80, 1
  %87 = icmp eq i64 %86, %1
  br i1 %87, label %92, label %79, !llvm.loop !33

88:                                               ; preds = %79, %59, %56
  %89 = phi i64 [ %57, %56 ], [ %57, %59 ], [ %80, %79 ]
  %90 = icmp eq i64 %89, %1
  br i1 %90, label %92, label %91

91:                                               ; preds = %88
  store i64 %89, ptr %3, align 8, !tbaa !6
  br label %1033

92:                                               ; preds = %27, %53, %85, %88
  call void @llvm.lifetime.start.p0(i64 768, ptr nonnull %5) #11
  br label %93

93:                                               ; preds = %92, %166
  %94 = phi i64 [ %9, %92 ], [ %177, %166 ]
  %95 = phi i64 [ 0, %92 ], [ %176, %166 ]
  %96 = phi i64 [ 0, %92 ], [ %175, %166 ]
  %97 = phi i64 [ 0, %92 ], [ %174, %166 ]
  %98 = phi i64 [ 0, %92 ], [ %168, %166 ]
  %99 = phi i64 [ 0, %92 ], [ %173, %166 ]
  %100 = phi i64 [ 0, %92 ], [ %172, %166 ]
  %101 = phi i32 [ 0, %92 ], [ %171, %166 ]
  %102 = phi i32 [ 0, %92 ], [ %170, %166 ]
  %103 = phi i32 [ 0, %92 ], [ %169, %166 ]
  br label %104

104:                                              ; preds = %161, %93
  %105 = phi i64 [ %94, %93 ], [ %163, %161 ]
  %106 = phi i64 [ %96, %93 ], [ %128, %161 ]
  %107 = phi i64 [ %97, %93 ], [ %129, %161 ]
  %108 = phi i64 [ %98, %93 ], [ %131, %161 ]
  %109 = phi i32 [ %101, %93 ], [ 1, %161 ]
  %110 = phi i32 [ %102, %93 ], [ 0, %161 ]
  %111 = icmp ne i32 %109, 0
  %112 = zext i1 %111 to i64
  %113 = getelementptr inbounds nuw i8, ptr %0, i64 %105
  %114 = load i8, ptr %113, align 1, !tbaa !12
  %115 = add i8 %114, -48
  %116 = icmp ult i8 %115, 10
  br i1 %116, label %117, label %159

117:                                              ; preds = %104
  %118 = add i64 %106, 1
  %119 = add i64 %107, %112
  %120 = icmp eq i32 %110, 0
  %121 = icmp eq i8 %115, 0
  %122 = and i1 %120, %121
  br i1 %122, label %123, label %140

123:                                              ; preds = %117
  %124 = add i64 %105, 1
  %125 = icmp eq i64 %124, %1
  br i1 %125, label %186, label %126

126:                                              ; preds = %123, %179
  %127 = phi i64 [ %180, %179 ], [ %124, %123 ]
  %128 = phi i64 [ %137, %179 ], [ %118, %123 ]
  %129 = phi i64 [ %138, %179 ], [ %119, %123 ]
  %130 = phi i64 [ %131, %179 ], [ %108, %123 ]
  %131 = add i64 %130, 1
  %132 = getelementptr inbounds nuw i8, ptr %0, i64 %127
  %133 = load i8, ptr %132, align 1, !tbaa !12
  %134 = add i8 %133, -48
  %135 = icmp ult i8 %134, 10
  br i1 %135, label %136, label %161

136:                                              ; preds = %126
  %137 = add i64 %128, 1
  %138 = add i64 %129, %112
  %139 = icmp eq i8 %134, 0
  br i1 %139, label %179, label %142

140:                                              ; preds = %117
  %141 = select i1 %121, i32 %103, i32 1
  br label %142

142:                                              ; preds = %136, %140
  %143 = phi i64 [ %118, %140 ], [ %137, %136 ]
  %144 = phi i64 [ %119, %140 ], [ %138, %136 ]
  %145 = phi i32 [ %141, %140 ], [ 1, %136 ]
  %146 = phi i64 [ %105, %140 ], [ %127, %136 ]
  %147 = phi i64 [ %108, %140 ], [ %131, %136 ]
  %148 = phi i8 [ %115, %140 ], [ %134, %136 ]
  %149 = icmp ult i64 %95, 768
  br i1 %149, label %150, label %166

150:                                              ; preds = %142
  %151 = add nuw nsw i64 %95, 1
  %152 = getelementptr inbounds nuw [768 x i8], ptr %5, i64 0, i64 %95
  store i8 %148, ptr %152, align 1, !tbaa !12
  %153 = icmp ult i64 %100, 19
  br i1 %153, label %154, label %166

154:                                              ; preds = %150
  %155 = mul i64 %99, 10
  %156 = zext nneg i8 %148 to i64
  %157 = add i64 %155, %156
  %158 = add nuw nsw i64 %100, 1
  br label %166

159:                                              ; preds = %104
  %160 = icmp eq i8 %114, 46
  br i1 %160, label %166, label %182

161:                                              ; preds = %126
  %162 = icmp ne i8 %133, 46
  %163 = add i64 %127, 1
  %164 = icmp eq i64 %163, %1
  %165 = or i1 %162, %164
  br i1 %165, label %186, label %104, !llvm.loop !34

166:                                              ; preds = %142, %159, %154, %150
  %167 = phi i64 [ %146, %150 ], [ %146, %154 ], [ %105, %159 ], [ %146, %142 ]
  %168 = phi i64 [ %147, %150 ], [ %147, %154 ], [ %108, %159 ], [ %147, %142 ]
  %169 = phi i32 [ %103, %150 ], [ %103, %154 ], [ %103, %159 ], [ %145, %142 ]
  %170 = phi i32 [ 1, %150 ], [ 1, %154 ], [ %110, %159 ], [ 1, %142 ]
  %171 = phi i32 [ %109, %150 ], [ %109, %154 ], [ 1, %159 ], [ %109, %142 ]
  %172 = phi i64 [ %100, %150 ], [ %158, %154 ], [ %100, %159 ], [ %100, %142 ]
  %173 = phi i64 [ %99, %150 ], [ %157, %154 ], [ %99, %159 ], [ %99, %142 ]
  %174 = phi i64 [ %144, %150 ], [ %144, %154 ], [ %107, %159 ], [ %144, %142 ]
  %175 = phi i64 [ %143, %150 ], [ %143, %154 ], [ %106, %159 ], [ %143, %142 ]
  %176 = phi i64 [ %151, %150 ], [ %151, %154 ], [ %95, %159 ], [ %95, %142 ]
  %177 = add i64 %167, 1
  %178 = icmp eq i64 %177, %1
  br i1 %178, label %184, label %93, !llvm.loop !34

179:                                              ; preds = %136
  %180 = add i64 %127, 1
  %181 = icmp eq i64 %180, %1
  br i1 %181, label %186, label %126, !llvm.loop !35

182:                                              ; preds = %159
  %183 = icmp eq i32 %110, 0
  br i1 %183, label %186, label %188

184:                                              ; preds = %166
  %185 = icmp eq i32 %170, 0
  br i1 %185, label %186, label %284

186:                                              ; preds = %161, %123, %179, %184, %182
  %187 = select i1 %8, double -0.000000e+00, double 0.000000e+00
  br label %1031

188:                                              ; preds = %182
  %189 = add nuw i64 %105, 1
  %190 = icmp ult i64 %189, %1
  br i1 %190, label %191, label %197

191:                                              ; preds = %188
  %192 = getelementptr inbounds nuw i8, ptr %0, i64 %189
  %193 = load i8, ptr %192, align 1, !tbaa !12
  switch i8 %193, label %197 [
    i8 43, label %194
    i8 45, label %194
  ]

194:                                              ; preds = %191, %191
  %195 = icmp ne i8 %193, 45
  %196 = add nuw i64 %105, 2
  br label %197

197:                                              ; preds = %194, %191, %188
  %198 = phi i1 [ %195, %194 ], [ true, %188 ], [ true, %191 ]
  %199 = phi i64 [ %196, %194 ], [ %189, %188 ], [ %189, %191 ]
  %200 = icmp ult i64 %199, %1
  br i1 %200, label %201, label %280

201:                                              ; preds = %197
  %202 = sub nuw i64 %1, %199
  %203 = and i64 %202, 3
  %204 = sub i64 %199, %1
  %205 = icmp ugt i64 %204, -4
  br i1 %205, label %258, label %206

206:                                              ; preds = %201
  %207 = and i64 %202, -4
  %208 = getelementptr i8, ptr %0, i64 1
  %209 = getelementptr i8, ptr %0, i64 2
  %210 = getelementptr i8, ptr %0, i64 3
  br label %211

211:                                              ; preds = %253, %206
  %212 = phi i64 [ %199, %206 ], [ %255, %253 ]
  %213 = phi i64 [ 0, %206 ], [ %254, %253 ]
  %214 = phi i64 [ 0, %206 ], [ %256, %253 ]
  %215 = icmp slt i64 %213, 1000000
  br i1 %215, label %216, label %223

216:                                              ; preds = %211
  %217 = mul i64 %213, 10
  %218 = getelementptr inbounds nuw i8, ptr %0, i64 %212
  %219 = load i8, ptr %218, align 1, !tbaa !12
  %220 = zext i8 %219 to i64
  %221 = add i64 %217, -48
  %222 = add i64 %221, %220
  br label %223

223:                                              ; preds = %216, %211
  %224 = phi i64 [ %222, %216 ], [ %213, %211 ]
  %225 = icmp slt i64 %224, 1000000
  br i1 %225, label %226, label %233

226:                                              ; preds = %223
  %227 = mul i64 %224, 10
  %228 = getelementptr i8, ptr %208, i64 %212
  %229 = load i8, ptr %228, align 1, !tbaa !12
  %230 = zext i8 %229 to i64
  %231 = add i64 %227, -48
  %232 = add i64 %231, %230
  br label %233

233:                                              ; preds = %226, %223
  %234 = phi i64 [ %232, %226 ], [ %224, %223 ]
  %235 = icmp slt i64 %234, 1000000
  br i1 %235, label %236, label %243

236:                                              ; preds = %233
  %237 = mul i64 %234, 10
  %238 = getelementptr i8, ptr %209, i64 %212
  %239 = load i8, ptr %238, align 1, !tbaa !12
  %240 = zext i8 %239 to i64
  %241 = add i64 %237, -48
  %242 = add i64 %241, %240
  br label %243

243:                                              ; preds = %236, %233
  %244 = phi i64 [ %242, %236 ], [ %234, %233 ]
  %245 = icmp slt i64 %244, 1000000
  br i1 %245, label %246, label %253

246:                                              ; preds = %243
  %247 = mul i64 %244, 10
  %248 = getelementptr i8, ptr %210, i64 %212
  %249 = load i8, ptr %248, align 1, !tbaa !12
  %250 = zext i8 %249 to i64
  %251 = add i64 %247, -48
  %252 = add i64 %251, %250
  br label %253

253:                                              ; preds = %246, %243
  %254 = phi i64 [ %252, %246 ], [ %244, %243 ]
  %255 = add nuw i64 %212, 4
  %256 = add i64 %214, 4
  %257 = icmp eq i64 %256, %207
  br i1 %257, label %258, label %211, !llvm.loop !37

258:                                              ; preds = %253, %201
  %259 = phi i64 [ poison, %201 ], [ %254, %253 ]
  %260 = phi i64 [ %199, %201 ], [ %255, %253 ]
  %261 = phi i64 [ 0, %201 ], [ %254, %253 ]
  %262 = icmp eq i64 %203, 0
  br i1 %262, label %280, label %263

263:                                              ; preds = %258, %275
  %264 = phi i64 [ %277, %275 ], [ %260, %258 ]
  %265 = phi i64 [ %276, %275 ], [ %261, %258 ]
  %266 = phi i64 [ %278, %275 ], [ 0, %258 ]
  %267 = icmp slt i64 %265, 1000000
  br i1 %267, label %268, label %275

268:                                              ; preds = %263
  %269 = mul i64 %265, 10
  %270 = getelementptr inbounds nuw i8, ptr %0, i64 %264
  %271 = load i8, ptr %270, align 1, !tbaa !12
  %272 = zext i8 %271 to i64
  %273 = add i64 %269, -48
  %274 = add i64 %273, %272
  br label %275

275:                                              ; preds = %268, %263
  %276 = phi i64 [ %274, %268 ], [ %265, %263 ]
  %277 = add nuw i64 %264, 1
  %278 = add i64 %266, 1
  %279 = icmp eq i64 %278, %203
  br i1 %279, label %280, label %263, !llvm.loop !38

280:                                              ; preds = %258, %275, %197
  %281 = phi i64 [ 0, %197 ], [ %259, %258 ], [ %276, %275 ]
  %282 = sub i64 0, %281
  %283 = select i1 %198, i64 %281, i64 %282
  br label %284

284:                                              ; preds = %280, %184
  %285 = phi i64 [ %108, %280 ], [ %168, %184 ]
  %286 = phi i32 [ %103, %280 ], [ %169, %184 ]
  %287 = phi i64 [ %100, %280 ], [ %172, %184 ]
  %288 = phi i64 [ %99, %280 ], [ %173, %184 ]
  %289 = phi i64 [ %107, %280 ], [ %174, %184 ]
  %290 = phi i64 [ %106, %280 ], [ %175, %184 ]
  %291 = phi i64 [ %95, %280 ], [ %176, %184 ]
  %292 = phi i64 [ %283, %280 ], [ 0, %184 ]
  %293 = sub i64 %292, %289
  %294 = add i64 %285, %291
  %295 = sub i64 %290, %294
  %296 = add i64 %295, %293
  %297 = add i64 %291, -1
  %298 = add i64 %297, %296
  %299 = icmp sgt i64 %298, 308
  br i1 %299, label %300, label %302

300:                                              ; preds = %284
  %301 = select i1 %8, double 0xFFF0000000000000, double 0x7FF0000000000000
  br label %1031

302:                                              ; preds = %284
  %303 = icmp slt i64 %298, -324
  br i1 %303, label %304, label %306

304:                                              ; preds = %302
  %305 = select i1 %8, double -0.000000e+00, double 0.000000e+00
  br label %1031

306:                                              ; preds = %302
  call void @llvm.lifetime.start.p0(i64 1568, ptr nonnull %6) #11
  %307 = getelementptr inbounds nuw i8, ptr %6, i64 1560
  store i32 %286, ptr %307, align 8, !tbaa !40
  %308 = getelementptr inbounds nuw i8, ptr %6, i64 1552
  store i64 %296, ptr %308, align 8, !tbaa !43
  %309 = getelementptr inbounds nuw i8, ptr %6, i64 768
  %310 = icmp eq i64 %291, 0
  br i1 %310, label %483, label %313

311:                                              ; preds = %399
  store i32 %400, ptr %309, align 8
  %312 = icmp eq i32 %402, 0
  br i1 %312, label %485, label %405

313:                                              ; preds = %306, %399
  %314 = phi i64 [ %403, %399 ], [ 0, %306 ]
  %315 = phi i32 [ %402, %399 ], [ 0, %306 ]
  %316 = phi i64 [ %401, %399 ], [ 0, %306 ]
  %317 = phi i32 [ %400, %399 ], [ 0, %306 ]
  %318 = mul i64 %316, 10
  %319 = getelementptr inbounds nuw [768 x i8], ptr %5, i64 0, i64 %314
  %320 = load i8, ptr %319, align 1, !tbaa !12
  %321 = zext i8 %320 to i64
  %322 = add i64 %318, %321
  %323 = add i32 %315, 1
  %324 = icmp eq i32 %323, 19
  br i1 %324, label %325, label %399

325:                                              ; preds = %313
  %326 = zext i64 %322 to i128
  %327 = icmp sgt i32 %317, 0
  br i1 %327, label %328, label %353

328:                                              ; preds = %325
  %329 = zext nneg i32 %317 to i64
  %330 = and i64 %329, 3
  %331 = icmp ult i32 %317, 4
  br i1 %331, label %334, label %332

332:                                              ; preds = %328
  %333 = and i64 %329, 2147483644
  br label %361

334:                                              ; preds = %361, %328
  %335 = phi i128 [ poison, %328 ], [ %395, %361 ]
  %336 = phi i64 [ 0, %328 ], [ %396, %361 ]
  %337 = phi i128 [ %326, %328 ], [ %395, %361 ]
  %338 = icmp eq i64 %330, 0
  br i1 %338, label %353, label %339

339:                                              ; preds = %334, %339
  %340 = phi i64 [ %350, %339 ], [ %336, %334 ]
  %341 = phi i128 [ %349, %339 ], [ %337, %334 ]
  %342 = phi i64 [ %351, %339 ], [ 0, %334 ]
  %343 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %340
  %344 = load i64, ptr %343, align 8, !tbaa !6
  %345 = zext i64 %344 to i128
  %346 = mul nuw i128 %345, 10000000000000000000
  %347 = add nuw i128 %346, %341
  %348 = trunc i128 %347 to i64
  store i64 %348, ptr %343, align 8, !tbaa !6
  %349 = lshr i128 %347, 64
  %350 = add nuw nsw i64 %340, 1
  %351 = add i64 %342, 1
  %352 = icmp eq i64 %351, %330
  br i1 %352, label %353, label %339, !llvm.loop !44

353:                                              ; preds = %334, %339, %325
  %354 = phi i128 [ %326, %325 ], [ %335, %334 ], [ %349, %339 ]
  %355 = icmp eq i128 %354, 0
  br i1 %355, label %399, label %356

356:                                              ; preds = %353
  %357 = trunc nuw i128 %354 to i64
  %358 = sext i32 %317 to i64
  %359 = getelementptr inbounds [96 x i64], ptr %6, i64 0, i64 %358
  store i64 %357, ptr %359, align 8, !tbaa !6
  %360 = add i32 %317, 1
  br label %399

361:                                              ; preds = %361, %332
  %362 = phi i64 [ 0, %332 ], [ %396, %361 ]
  %363 = phi i128 [ %326, %332 ], [ %395, %361 ]
  %364 = phi i64 [ 0, %332 ], [ %397, %361 ]
  %365 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %362
  %366 = load i64, ptr %365, align 8, !tbaa !6
  %367 = zext i64 %366 to i128
  %368 = mul nuw i128 %367, 10000000000000000000
  %369 = add nuw i128 %368, %363
  %370 = trunc i128 %369 to i64
  store i64 %370, ptr %365, align 8, !tbaa !6
  %371 = lshr i128 %369, 64
  %372 = or disjoint i64 %362, 1
  %373 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %372
  %374 = load i64, ptr %373, align 8, !tbaa !6
  %375 = zext i64 %374 to i128
  %376 = mul nuw i128 %375, 10000000000000000000
  %377 = add nuw i128 %376, %371
  %378 = trunc i128 %377 to i64
  store i64 %378, ptr %373, align 8, !tbaa !6
  %379 = lshr i128 %377, 64
  %380 = or disjoint i64 %362, 2
  %381 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %380
  %382 = load i64, ptr %381, align 8, !tbaa !6
  %383 = zext i64 %382 to i128
  %384 = mul nuw i128 %383, 10000000000000000000
  %385 = add nuw i128 %384, %379
  %386 = trunc i128 %385 to i64
  store i64 %386, ptr %381, align 8, !tbaa !6
  %387 = lshr i128 %385, 64
  %388 = or disjoint i64 %362, 3
  %389 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %388
  %390 = load i64, ptr %389, align 8, !tbaa !6
  %391 = zext i64 %390 to i128
  %392 = mul nuw i128 %391, 10000000000000000000
  %393 = add nuw i128 %392, %387
  %394 = trunc i128 %393 to i64
  store i64 %394, ptr %389, align 8, !tbaa !6
  %395 = lshr i128 %393, 64
  %396 = add nuw nsw i64 %362, 4
  %397 = add i64 %364, 4
  %398 = icmp eq i64 %397, %333
  br i1 %398, label %334, label %361, !llvm.loop !45

399:                                              ; preds = %356, %353, %313
  %400 = phi i32 [ %317, %313 ], [ %317, %353 ], [ %360, %356 ]
  %401 = phi i64 [ %322, %313 ], [ 0, %353 ], [ 0, %356 ]
  %402 = phi i32 [ %323, %313 ], [ 0, %353 ], [ 0, %356 ]
  %403 = add nuw i64 %314, 1
  %404 = icmp eq i64 %403, %291
  br i1 %404, label %311, label %313, !llvm.loop !46

405:                                              ; preds = %311
  %406 = zext i64 %401 to i128
  %407 = icmp sgt i32 %400, 0
  br i1 %407, label %408, label %437

408:                                              ; preds = %405
  %409 = sext i32 %402 to i64
  %410 = getelementptr inbounds [20 x i64], ptr @NUMF_EL1_P10, i64 0, i64 %409
  %411 = load i64, ptr %410, align 8, !tbaa !6
  %412 = zext i64 %411 to i128
  %413 = zext nneg i32 %400 to i64
  %414 = and i64 %413, 3
  %415 = icmp ult i32 %400, 4
  br i1 %415, label %418, label %416

416:                                              ; preds = %408
  %417 = and i64 %413, 2147483644
  br label %445

418:                                              ; preds = %445, %408
  %419 = phi i128 [ poison, %408 ], [ %479, %445 ]
  %420 = phi i64 [ 0, %408 ], [ %480, %445 ]
  %421 = phi i128 [ %406, %408 ], [ %479, %445 ]
  %422 = icmp eq i64 %414, 0
  br i1 %422, label %437, label %423

423:                                              ; preds = %418, %423
  %424 = phi i64 [ %434, %423 ], [ %420, %418 ]
  %425 = phi i128 [ %433, %423 ], [ %421, %418 ]
  %426 = phi i64 [ %435, %423 ], [ 0, %418 ]
  %427 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %424
  %428 = load i64, ptr %427, align 8, !tbaa !6
  %429 = zext i64 %428 to i128
  %430 = mul nuw i128 %429, %412
  %431 = add nuw i128 %430, %425
  %432 = trunc i128 %431 to i64
  store i64 %432, ptr %427, align 8, !tbaa !6
  %433 = lshr i128 %431, 64
  %434 = add nuw nsw i64 %424, 1
  %435 = add i64 %426, 1
  %436 = icmp eq i64 %435, %414
  br i1 %436, label %437, label %423, !llvm.loop !47

437:                                              ; preds = %418, %423, %405
  %438 = phi i128 [ %406, %405 ], [ %419, %418 ], [ %433, %423 ]
  %439 = icmp eq i128 %438, 0
  br i1 %439, label %485, label %440

440:                                              ; preds = %437
  %441 = trunc nuw i128 %438 to i64
  %442 = sext i32 %400 to i64
  %443 = getelementptr inbounds [96 x i64], ptr %6, i64 0, i64 %442
  store i64 %441, ptr %443, align 8, !tbaa !6
  %444 = add i32 %400, 1
  br label %483

445:                                              ; preds = %445, %416
  %446 = phi i64 [ 0, %416 ], [ %480, %445 ]
  %447 = phi i128 [ %406, %416 ], [ %479, %445 ]
  %448 = phi i64 [ 0, %416 ], [ %481, %445 ]
  %449 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %446
  %450 = load i64, ptr %449, align 8, !tbaa !6
  %451 = zext i64 %450 to i128
  %452 = mul nuw i128 %451, %412
  %453 = add nuw i128 %452, %447
  %454 = trunc i128 %453 to i64
  store i64 %454, ptr %449, align 8, !tbaa !6
  %455 = lshr i128 %453, 64
  %456 = or disjoint i64 %446, 1
  %457 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %456
  %458 = load i64, ptr %457, align 8, !tbaa !6
  %459 = zext i64 %458 to i128
  %460 = mul nuw i128 %459, %412
  %461 = add nuw i128 %460, %455
  %462 = trunc i128 %461 to i64
  store i64 %462, ptr %457, align 8, !tbaa !6
  %463 = lshr i128 %461, 64
  %464 = or disjoint i64 %446, 2
  %465 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %464
  %466 = load i64, ptr %465, align 8, !tbaa !6
  %467 = zext i64 %466 to i128
  %468 = mul nuw i128 %467, %412
  %469 = add nuw i128 %468, %463
  %470 = trunc i128 %469 to i64
  store i64 %470, ptr %465, align 8, !tbaa !6
  %471 = lshr i128 %469, 64
  %472 = or disjoint i64 %446, 3
  %473 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %472
  %474 = load i64, ptr %473, align 8, !tbaa !6
  %475 = zext i64 %474 to i128
  %476 = mul nuw i128 %475, %412
  %477 = add nuw i128 %476, %471
  %478 = trunc i128 %477 to i64
  store i64 %478, ptr %473, align 8, !tbaa !6
  %479 = lshr i128 %477, 64
  %480 = add nuw nsw i64 %446, 4
  %481 = add i64 %448, 4
  %482 = icmp eq i64 %481, %417
  br i1 %482, label %418, label %445, !llvm.loop !45

483:                                              ; preds = %306, %440
  %484 = phi i32 [ %444, %440 ], [ 0, %306 ]
  store i32 %484, ptr %309, align 8
  br label %485

485:                                              ; preds = %483, %437, %311
  %486 = getelementptr inbounds nuw i8, ptr %6, i64 776
  store i64 1, ptr %486, align 8, !tbaa !6
  %487 = getelementptr inbounds nuw i8, ptr %6, i64 1544
  store i32 1, ptr %487, align 8, !tbaa !48
  %488 = icmp eq i32 %286, 0
  br i1 %488, label %662, label %489

489:                                              ; preds = %485
  %490 = sub i64 0, %296
  %491 = icmp sgt i64 %490, 26
  br i1 %491, label %492, label %579

492:                                              ; preds = %489, %571
  %493 = phi i64 [ %573, %571 ], [ %490, %489 ]
  %494 = phi i32 [ %572, %571 ], [ 1, %489 ]
  %495 = icmp sgt i32 %494, 0
  br i1 %495, label %496, label %571

496:                                              ; preds = %492
  %497 = zext nneg i32 %494 to i64
  %498 = and i64 %497, 3
  %499 = icmp ult i32 %494, 4
  br i1 %499, label %504, label %500

500:                                              ; preds = %496
  %501 = and i64 %497, 2147483644
  br label %533

502:                                              ; preds = %533
  %503 = trunc nuw i128 %567 to i64
  br label %504

504:                                              ; preds = %502, %496
  %505 = phi i128 [ poison, %496 ], [ %565, %502 ]
  %506 = phi i64 [ poison, %496 ], [ %503, %502 ]
  %507 = phi i64 [ 0, %496 ], [ %568, %502 ]
  %508 = phi i128 [ 0, %496 ], [ %567, %502 ]
  %509 = icmp eq i64 %498, 0
  br i1 %509, label %526, label %510

510:                                              ; preds = %504, %510
  %511 = phi i64 [ %521, %510 ], [ %507, %504 ]
  %512 = phi i128 [ %520, %510 ], [ %508, %504 ]
  %513 = phi i64 [ %522, %510 ], [ 0, %504 ]
  %514 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %511
  %515 = load i64, ptr %514, align 8, !tbaa !6
  %516 = zext i64 %515 to i128
  %517 = mul nuw nsw i128 %516, 7450580596923828125
  %518 = add nuw nsw i128 %517, %512
  %519 = trunc i128 %518 to i64
  store i64 %519, ptr %514, align 8, !tbaa !6
  %520 = lshr i128 %518, 64
  %521 = add nuw nsw i64 %511, 1
  %522 = add i64 %513, 1
  %523 = icmp eq i64 %522, %498
  br i1 %523, label %524, label %510, !llvm.loop !49

524:                                              ; preds = %510
  %525 = trunc nuw i128 %520 to i64
  br label %526

526:                                              ; preds = %504, %524
  %527 = phi i128 [ %505, %504 ], [ %518, %524 ]
  %528 = phi i64 [ %506, %504 ], [ %525, %524 ]
  %529 = icmp samesign ult i128 %527, 18446744073709551616
  br i1 %529, label %571, label %530

530:                                              ; preds = %526
  %531 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %497
  store i64 %528, ptr %531, align 8, !tbaa !6
  %532 = add nuw i32 %494, 1
  br label %571

533:                                              ; preds = %533, %500
  %534 = phi i64 [ 0, %500 ], [ %568, %533 ]
  %535 = phi i128 [ 0, %500 ], [ %567, %533 ]
  %536 = phi i64 [ 0, %500 ], [ %569, %533 ]
  %537 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %534
  %538 = load i64, ptr %537, align 8, !tbaa !6
  %539 = zext i64 %538 to i128
  %540 = mul nuw nsw i128 %539, 7450580596923828125
  %541 = add nuw nsw i128 %540, %535
  %542 = trunc i128 %541 to i64
  store i64 %542, ptr %537, align 8, !tbaa !6
  %543 = lshr i128 %541, 64
  %544 = or disjoint i64 %534, 1
  %545 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %544
  %546 = load i64, ptr %545, align 8, !tbaa !6
  %547 = zext i64 %546 to i128
  %548 = mul nuw nsw i128 %547, 7450580596923828125
  %549 = add nuw nsw i128 %548, %543
  %550 = trunc i128 %549 to i64
  store i64 %550, ptr %545, align 8, !tbaa !6
  %551 = lshr i128 %549, 64
  %552 = or disjoint i64 %534, 2
  %553 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %552
  %554 = load i64, ptr %553, align 8, !tbaa !6
  %555 = zext i64 %554 to i128
  %556 = mul nuw nsw i128 %555, 7450580596923828125
  %557 = add nuw nsw i128 %556, %551
  %558 = trunc i128 %557 to i64
  store i64 %558, ptr %553, align 8, !tbaa !6
  %559 = lshr i128 %557, 64
  %560 = or disjoint i64 %534, 3
  %561 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %560
  %562 = load i64, ptr %561, align 8, !tbaa !6
  %563 = zext i64 %562 to i128
  %564 = mul nuw nsw i128 %563, 7450580596923828125
  %565 = add nuw nsw i128 %564, %559
  %566 = trunc i128 %565 to i64
  store i64 %566, ptr %561, align 8, !tbaa !6
  %567 = lshr i128 %565, 64
  %568 = add nuw nsw i64 %534, 4
  %569 = add i64 %536, 4
  %570 = icmp eq i64 %569, %501
  br i1 %570, label %502, label %533, !llvm.loop !45

571:                                              ; preds = %530, %526, %492
  %572 = phi i32 [ %494, %492 ], [ %494, %526 ], [ %532, %530 ]
  %573 = add nsw i64 %493, -27
  %574 = icmp sgt i64 %493, 53
  br i1 %574, label %492, label %575, !llvm.loop !50

575:                                              ; preds = %571
  store i32 %572, ptr %487, align 8
  %576 = icmp ne i64 %573, 0
  %577 = icmp sgt i32 %572, 0
  %578 = select i1 %576, i1 %577, i1 false
  br i1 %578, label %581, label %928

579:                                              ; preds = %489
  store i32 1, ptr %487, align 8
  %580 = icmp eq i64 %296, 0
  br i1 %580, label %928, label %581

581:                                              ; preds = %579, %575
  %582 = phi i32 [ 1, %579 ], [ %572, %575 ]
  %583 = phi i64 [ %490, %579 ], [ %573, %575 ]
  %584 = getelementptr inbounds [27 x i64], ptr @STK_P5, i64 0, i64 %583
  %585 = load i64, ptr %584, align 8, !tbaa !6
  %586 = zext i64 %585 to i128
  %587 = zext nneg i32 %582 to i64
  %588 = and i64 %587, 3
  %589 = add i32 %582, -1
  %590 = icmp ult i32 %589, 3
  br i1 %590, label %595, label %591

591:                                              ; preds = %581
  %592 = and i64 %587, 2147483644
  br label %624

593:                                              ; preds = %624
  %594 = trunc nuw i128 %658 to i64
  br label %595

595:                                              ; preds = %593, %581
  %596 = phi i128 [ poison, %581 ], [ %656, %593 ]
  %597 = phi i64 [ poison, %581 ], [ %594, %593 ]
  %598 = phi i64 [ 0, %581 ], [ %659, %593 ]
  %599 = phi i128 [ 0, %581 ], [ %658, %593 ]
  %600 = icmp eq i64 %588, 0
  br i1 %600, label %617, label %601

601:                                              ; preds = %595, %601
  %602 = phi i64 [ %612, %601 ], [ %598, %595 ]
  %603 = phi i128 [ %611, %601 ], [ %599, %595 ]
  %604 = phi i64 [ %613, %601 ], [ 0, %595 ]
  %605 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %602
  %606 = load i64, ptr %605, align 8, !tbaa !6
  %607 = zext i64 %606 to i128
  %608 = mul nuw i128 %607, %586
  %609 = add nuw i128 %608, %603
  %610 = trunc i128 %609 to i64
  store i64 %610, ptr %605, align 8, !tbaa !6
  %611 = lshr i128 %609, 64
  %612 = add nuw nsw i64 %602, 1
  %613 = add i64 %604, 1
  %614 = icmp eq i64 %613, %588
  br i1 %614, label %615, label %601, !llvm.loop !51

615:                                              ; preds = %601
  %616 = trunc nuw i128 %611 to i64
  br label %617

617:                                              ; preds = %595, %615
  %618 = phi i128 [ %596, %595 ], [ %609, %615 ]
  %619 = phi i64 [ %597, %595 ], [ %616, %615 ]
  %620 = icmp ult i128 %618, 18446744073709551616
  br i1 %620, label %928, label %621

621:                                              ; preds = %617
  %622 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %587
  store i64 %619, ptr %622, align 8, !tbaa !6
  %623 = add nuw i32 %582, 1
  store i32 %623, ptr %487, align 8, !tbaa !48
  br label %928

624:                                              ; preds = %624, %591
  %625 = phi i64 [ 0, %591 ], [ %659, %624 ]
  %626 = phi i128 [ 0, %591 ], [ %658, %624 ]
  %627 = phi i64 [ 0, %591 ], [ %660, %624 ]
  %628 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %625
  %629 = load i64, ptr %628, align 8, !tbaa !6
  %630 = zext i64 %629 to i128
  %631 = mul nuw i128 %630, %586
  %632 = add nuw i128 %631, %626
  %633 = trunc i128 %632 to i64
  store i64 %633, ptr %628, align 8, !tbaa !6
  %634 = lshr i128 %632, 64
  %635 = or disjoint i64 %625, 1
  %636 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %635
  %637 = load i64, ptr %636, align 8, !tbaa !6
  %638 = zext i64 %637 to i128
  %639 = mul nuw i128 %638, %586
  %640 = add nuw i128 %639, %634
  %641 = trunc i128 %640 to i64
  store i64 %641, ptr %636, align 8, !tbaa !6
  %642 = lshr i128 %640, 64
  %643 = or disjoint i64 %625, 2
  %644 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %643
  %645 = load i64, ptr %644, align 8, !tbaa !6
  %646 = zext i64 %645 to i128
  %647 = mul nuw i128 %646, %586
  %648 = add nuw i128 %647, %642
  %649 = trunc i128 %648 to i64
  store i64 %649, ptr %644, align 8, !tbaa !6
  %650 = lshr i128 %648, 64
  %651 = or disjoint i64 %625, 3
  %652 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %651
  %653 = load i64, ptr %652, align 8, !tbaa !6
  %654 = zext i64 %653 to i128
  %655 = mul nuw i128 %654, %586
  %656 = add nuw i128 %655, %650
  %657 = trunc i128 %656 to i64
  store i64 %657, ptr %652, align 8, !tbaa !6
  %658 = lshr i128 %656, 64
  %659 = add nuw nsw i64 %625, 4
  %660 = add i64 %627, 4
  %661 = icmp eq i64 %660, %592
  br i1 %661, label %593, label %624, !llvm.loop !45

662:                                              ; preds = %485
  %663 = icmp slt i64 %296, 0
  br i1 %663, label %667, label %664

664:                                              ; preds = %662
  %665 = load i32, ptr %309, align 8
  %666 = icmp samesign ugt i64 %296, 18
  br i1 %666, label %760, label %843

667:                                              ; preds = %662
  %668 = sub i64 0, %296
  %669 = icmp sgt i64 %668, 18
  br i1 %669, label %671, label %670

670:                                              ; preds = %667
  store i32 1, ptr %487, align 8
  br label %756

671:                                              ; preds = %667, %750
  %672 = phi i64 [ %752, %750 ], [ %668, %667 ]
  %673 = phi i32 [ %751, %750 ], [ 1, %667 ]
  %674 = icmp sgt i32 %673, 0
  br i1 %674, label %675, label %750

675:                                              ; preds = %671
  %676 = zext nneg i32 %673 to i64
  %677 = and i64 %676, 3
  %678 = icmp ult i32 %673, 4
  br i1 %678, label %683, label %679

679:                                              ; preds = %675
  %680 = and i64 %676, 2147483644
  br label %712

681:                                              ; preds = %712
  %682 = trunc nuw i128 %746 to i64
  br label %683

683:                                              ; preds = %681, %675
  %684 = phi i128 [ poison, %675 ], [ %744, %681 ]
  %685 = phi i64 [ poison, %675 ], [ %682, %681 ]
  %686 = phi i64 [ 0, %675 ], [ %747, %681 ]
  %687 = phi i128 [ 0, %675 ], [ %746, %681 ]
  %688 = icmp eq i64 %677, 0
  br i1 %688, label %705, label %689

689:                                              ; preds = %683, %689
  %690 = phi i64 [ %700, %689 ], [ %686, %683 ]
  %691 = phi i128 [ %699, %689 ], [ %687, %683 ]
  %692 = phi i64 [ %701, %689 ], [ 0, %683 ]
  %693 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %690
  %694 = load i64, ptr %693, align 8, !tbaa !6
  %695 = zext i64 %694 to i128
  %696 = mul nuw i128 %695, 10000000000000000000
  %697 = add nuw i128 %696, %691
  %698 = trunc i128 %697 to i64
  store i64 %698, ptr %693, align 8, !tbaa !6
  %699 = lshr i128 %697, 64
  %700 = add nuw nsw i64 %690, 1
  %701 = add i64 %692, 1
  %702 = icmp eq i64 %701, %677
  br i1 %702, label %703, label %689, !llvm.loop !52

703:                                              ; preds = %689
  %704 = trunc nuw i128 %699 to i64
  br label %705

705:                                              ; preds = %683, %703
  %706 = phi i128 [ %684, %683 ], [ %697, %703 ]
  %707 = phi i64 [ %685, %683 ], [ %704, %703 ]
  %708 = icmp ult i128 %706, 18446744073709551616
  br i1 %708, label %750, label %709

709:                                              ; preds = %705
  %710 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %676
  store i64 %707, ptr %710, align 8, !tbaa !6
  %711 = add nuw i32 %673, 1
  br label %750

712:                                              ; preds = %712, %679
  %713 = phi i64 [ 0, %679 ], [ %747, %712 ]
  %714 = phi i128 [ 0, %679 ], [ %746, %712 ]
  %715 = phi i64 [ 0, %679 ], [ %748, %712 ]
  %716 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %713
  %717 = load i64, ptr %716, align 8, !tbaa !6
  %718 = zext i64 %717 to i128
  %719 = mul nuw i128 %718, 10000000000000000000
  %720 = add nuw i128 %719, %714
  %721 = trunc i128 %720 to i64
  store i64 %721, ptr %716, align 8, !tbaa !6
  %722 = lshr i128 %720, 64
  %723 = or disjoint i64 %713, 1
  %724 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %723
  %725 = load i64, ptr %724, align 8, !tbaa !6
  %726 = zext i64 %725 to i128
  %727 = mul nuw i128 %726, 10000000000000000000
  %728 = add nuw i128 %727, %722
  %729 = trunc i128 %728 to i64
  store i64 %729, ptr %724, align 8, !tbaa !6
  %730 = lshr i128 %728, 64
  %731 = or disjoint i64 %713, 2
  %732 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %731
  %733 = load i64, ptr %732, align 8, !tbaa !6
  %734 = zext i64 %733 to i128
  %735 = mul nuw i128 %734, 10000000000000000000
  %736 = add nuw i128 %735, %730
  %737 = trunc i128 %736 to i64
  store i64 %737, ptr %732, align 8, !tbaa !6
  %738 = lshr i128 %736, 64
  %739 = or disjoint i64 %713, 3
  %740 = getelementptr inbounds nuw [96 x i64], ptr %486, i64 0, i64 %739
  %741 = load i64, ptr %740, align 8, !tbaa !6
  %742 = zext i64 %741 to i128
  %743 = mul nuw i128 %742, 10000000000000000000
  %744 = add nuw i128 %743, %738
  %745 = trunc i128 %744 to i64
  store i64 %745, ptr %740, align 8, !tbaa !6
  %746 = lshr i128 %744, 64
  %747 = add nuw nsw i64 %713, 4
  %748 = add i64 %715, 4
  %749 = icmp eq i64 %748, %680
  br i1 %749, label %681, label %712, !llvm.loop !45

750:                                              ; preds = %709, %705, %671
  %751 = phi i32 [ %673, %671 ], [ %673, %705 ], [ %711, %709 ]
  %752 = add nsw i64 %672, -19
  %753 = icmp sgt i64 %672, 37
  br i1 %753, label %671, label %754, !llvm.loop !53

754:                                              ; preds = %750
  store i32 %751, ptr %487, align 8
  %755 = icmp eq i64 %752, 0
  br i1 %755, label %928, label %756

756:                                              ; preds = %754, %670
  %757 = phi i64 [ %668, %670 ], [ %752, %754 ]
  %758 = getelementptr inbounds [20 x i64], ptr @NUMF_EL1_P10, i64 0, i64 %757
  %759 = load i64, ptr %758, align 8, !tbaa !6
  call fastcc void @stk_mul_u64(ptr noundef %486, i64 noundef %759)
  br label %928

760:                                              ; preds = %664, %839
  %761 = phi i64 [ %841, %839 ], [ %296, %664 ]
  %762 = phi i32 [ %840, %839 ], [ %665, %664 ]
  %763 = icmp sgt i32 %762, 0
  br i1 %763, label %764, label %839

764:                                              ; preds = %760
  %765 = zext nneg i32 %762 to i64
  %766 = and i64 %765, 3
  %767 = icmp ult i32 %762, 4
  br i1 %767, label %772, label %768

768:                                              ; preds = %764
  %769 = and i64 %765, 2147483644
  br label %801

770:                                              ; preds = %801
  %771 = trunc nuw i128 %835 to i64
  br label %772

772:                                              ; preds = %770, %764
  %773 = phi i128 [ poison, %764 ], [ %833, %770 ]
  %774 = phi i64 [ poison, %764 ], [ %771, %770 ]
  %775 = phi i64 [ 0, %764 ], [ %836, %770 ]
  %776 = phi i128 [ 0, %764 ], [ %835, %770 ]
  %777 = icmp eq i64 %766, 0
  br i1 %777, label %794, label %778

778:                                              ; preds = %772, %778
  %779 = phi i64 [ %789, %778 ], [ %775, %772 ]
  %780 = phi i128 [ %788, %778 ], [ %776, %772 ]
  %781 = phi i64 [ %790, %778 ], [ 0, %772 ]
  %782 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %779
  %783 = load i64, ptr %782, align 8, !tbaa !6
  %784 = zext i64 %783 to i128
  %785 = mul nuw i128 %784, 10000000000000000000
  %786 = add nuw i128 %785, %780
  %787 = trunc i128 %786 to i64
  store i64 %787, ptr %782, align 8, !tbaa !6
  %788 = lshr i128 %786, 64
  %789 = add nuw nsw i64 %779, 1
  %790 = add i64 %781, 1
  %791 = icmp eq i64 %790, %766
  br i1 %791, label %792, label %778, !llvm.loop !54

792:                                              ; preds = %778
  %793 = trunc nuw i128 %788 to i64
  br label %794

794:                                              ; preds = %772, %792
  %795 = phi i128 [ %773, %772 ], [ %786, %792 ]
  %796 = phi i64 [ %774, %772 ], [ %793, %792 ]
  %797 = icmp ult i128 %795, 18446744073709551616
  br i1 %797, label %839, label %798

798:                                              ; preds = %794
  %799 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %765
  store i64 %796, ptr %799, align 8, !tbaa !6
  %800 = add nuw i32 %762, 1
  br label %839

801:                                              ; preds = %801, %768
  %802 = phi i64 [ 0, %768 ], [ %836, %801 ]
  %803 = phi i128 [ 0, %768 ], [ %835, %801 ]
  %804 = phi i64 [ 0, %768 ], [ %837, %801 ]
  %805 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %802
  %806 = load i64, ptr %805, align 8, !tbaa !6
  %807 = zext i64 %806 to i128
  %808 = mul nuw i128 %807, 10000000000000000000
  %809 = add nuw i128 %808, %803
  %810 = trunc i128 %809 to i64
  store i64 %810, ptr %805, align 8, !tbaa !6
  %811 = lshr i128 %809, 64
  %812 = or disjoint i64 %802, 1
  %813 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %812
  %814 = load i64, ptr %813, align 8, !tbaa !6
  %815 = zext i64 %814 to i128
  %816 = mul nuw i128 %815, 10000000000000000000
  %817 = add nuw i128 %816, %811
  %818 = trunc i128 %817 to i64
  store i64 %818, ptr %813, align 8, !tbaa !6
  %819 = lshr i128 %817, 64
  %820 = or disjoint i64 %802, 2
  %821 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %820
  %822 = load i64, ptr %821, align 8, !tbaa !6
  %823 = zext i64 %822 to i128
  %824 = mul nuw i128 %823, 10000000000000000000
  %825 = add nuw i128 %824, %819
  %826 = trunc i128 %825 to i64
  store i64 %826, ptr %821, align 8, !tbaa !6
  %827 = lshr i128 %825, 64
  %828 = or disjoint i64 %802, 3
  %829 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %828
  %830 = load i64, ptr %829, align 8, !tbaa !6
  %831 = zext i64 %830 to i128
  %832 = mul nuw i128 %831, 10000000000000000000
  %833 = add nuw i128 %832, %827
  %834 = trunc i128 %833 to i64
  store i64 %834, ptr %829, align 8, !tbaa !6
  %835 = lshr i128 %833, 64
  %836 = add nuw nsw i64 %802, 4
  %837 = add i64 %804, 4
  %838 = icmp eq i64 %837, %769
  br i1 %838, label %770, label %801, !llvm.loop !45

839:                                              ; preds = %798, %794, %760
  %840 = phi i32 [ %762, %760 ], [ %762, %794 ], [ %800, %798 ]
  %841 = add nsw i64 %761, -19
  %842 = icmp sgt i64 %761, 37
  br i1 %842, label %760, label %843, !llvm.loop !55

843:                                              ; preds = %839, %664
  %844 = phi i32 [ %665, %664 ], [ %840, %839 ]
  %845 = phi i64 [ %296, %664 ], [ %841, %839 ]
  store i32 %844, ptr %309, align 8
  %846 = icmp ne i64 %845, 0
  %847 = icmp sgt i32 %844, 0
  %848 = select i1 %846, i1 %847, i1 false
  br i1 %848, label %849, label %927

849:                                              ; preds = %843
  %850 = getelementptr inbounds nuw [20 x i64], ptr @NUMF_EL1_P10, i64 0, i64 %845
  %851 = load i64, ptr %850, align 8, !tbaa !6
  %852 = zext i64 %851 to i128
  %853 = zext nneg i32 %844 to i64
  %854 = and i64 %853, 3
  %855 = icmp ult i32 %844, 4
  br i1 %855, label %860, label %856

856:                                              ; preds = %849
  %857 = and i64 %853, 2147483644
  br label %889

858:                                              ; preds = %889
  %859 = trunc nuw i128 %923 to i64
  br label %860

860:                                              ; preds = %858, %849
  %861 = phi i128 [ poison, %849 ], [ %921, %858 ]
  %862 = phi i64 [ poison, %849 ], [ %859, %858 ]
  %863 = phi i64 [ 0, %849 ], [ %924, %858 ]
  %864 = phi i128 [ 0, %849 ], [ %923, %858 ]
  %865 = icmp eq i64 %854, 0
  br i1 %865, label %882, label %866

866:                                              ; preds = %860, %866
  %867 = phi i64 [ %877, %866 ], [ %863, %860 ]
  %868 = phi i128 [ %876, %866 ], [ %864, %860 ]
  %869 = phi i64 [ %878, %866 ], [ 0, %860 ]
  %870 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %867
  %871 = load i64, ptr %870, align 8, !tbaa !6
  %872 = zext i64 %871 to i128
  %873 = mul nuw i128 %872, %852
  %874 = add nuw i128 %873, %868
  %875 = trunc i128 %874 to i64
  store i64 %875, ptr %870, align 8, !tbaa !6
  %876 = lshr i128 %874, 64
  %877 = add nuw nsw i64 %867, 1
  %878 = add i64 %869, 1
  %879 = icmp eq i64 %878, %854
  br i1 %879, label %880, label %866, !llvm.loop !56

880:                                              ; preds = %866
  %881 = trunc nuw i128 %876 to i64
  br label %882

882:                                              ; preds = %860, %880
  %883 = phi i128 [ %861, %860 ], [ %874, %880 ]
  %884 = phi i64 [ %862, %860 ], [ %881, %880 ]
  %885 = icmp ult i128 %883, 18446744073709551616
  br i1 %885, label %927, label %886

886:                                              ; preds = %882
  %887 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %853
  store i64 %884, ptr %887, align 8, !tbaa !6
  %888 = add nuw i32 %844, 1
  store i32 %888, ptr %309, align 8, !tbaa !48
  br label %927

889:                                              ; preds = %889, %856
  %890 = phi i64 [ 0, %856 ], [ %924, %889 ]
  %891 = phi i128 [ 0, %856 ], [ %923, %889 ]
  %892 = phi i64 [ 0, %856 ], [ %925, %889 ]
  %893 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %890
  %894 = load i64, ptr %893, align 8, !tbaa !6
  %895 = zext i64 %894 to i128
  %896 = mul nuw i128 %895, %852
  %897 = add nuw i128 %896, %891
  %898 = trunc i128 %897 to i64
  store i64 %898, ptr %893, align 8, !tbaa !6
  %899 = lshr i128 %897, 64
  %900 = or disjoint i64 %890, 1
  %901 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %900
  %902 = load i64, ptr %901, align 8, !tbaa !6
  %903 = zext i64 %902 to i128
  %904 = mul nuw i128 %903, %852
  %905 = add nuw i128 %904, %899
  %906 = trunc i128 %905 to i64
  store i64 %906, ptr %901, align 8, !tbaa !6
  %907 = lshr i128 %905, 64
  %908 = or disjoint i64 %890, 2
  %909 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %908
  %910 = load i64, ptr %909, align 8, !tbaa !6
  %911 = zext i64 %910 to i128
  %912 = mul nuw i128 %911, %852
  %913 = add nuw i128 %912, %907
  %914 = trunc i128 %913 to i64
  store i64 %914, ptr %909, align 8, !tbaa !6
  %915 = lshr i128 %913, 64
  %916 = or disjoint i64 %890, 3
  %917 = getelementptr inbounds nuw [96 x i64], ptr %6, i64 0, i64 %916
  %918 = load i64, ptr %917, align 8, !tbaa !6
  %919 = zext i64 %918 to i128
  %920 = mul nuw i128 %919, %852
  %921 = add nuw i128 %920, %915
  %922 = trunc i128 %921 to i64
  store i64 %922, ptr %917, align 8, !tbaa !6
  %923 = lshr i128 %921, 64
  %924 = add nuw nsw i64 %890, 4
  %925 = add i64 %892, 4
  %926 = icmp eq i64 %925, %857
  br i1 %926, label %858, label %889, !llvm.loop !45

927:                                              ; preds = %886, %882, %843
  store i64 0, ptr %308, align 8, !tbaa !43
  br label %928

928:                                              ; preds = %927, %756, %754, %621, %617, %579, %575
  %929 = sub i64 %298, %287
  %930 = add i64 %929, 1
  %931 = uitofp i64 %288 to double
  br label %932

932:                                              ; preds = %936, %928
  %933 = phi i64 [ %930, %928 ], [ %941, %936 ]
  %934 = phi double [ %931, %928 ], [ %940, %936 ]
  %935 = icmp sgt i64 %933, 0
  br i1 %935, label %936, label %944

936:                                              ; preds = %932
  %937 = tail call i64 @llvm.umin.i64(i64 %933, i64 22)
  %938 = getelementptr inbounds nuw [23 x double], ptr @NUMF_EL1_POW10, i64 0, i64 %937
  %939 = load double, ptr %938, align 8, !tbaa !19
  %940 = fmul double %934, %939
  %941 = sub nsw i64 %933, %937
  %942 = bitcast double %940 to i64
  %943 = icmp ugt i64 %942, 9218868437227405311
  br i1 %943, label %944, label %932

944:                                              ; preds = %936, %932
  %945 = phi i64 [ %933, %932 ], [ %941, %936 ]
  %946 = phi double [ %934, %932 ], [ %940, %936 ]
  br label %947

947:                                              ; preds = %944, %951
  %948 = phi i64 [ %959, %951 ], [ %945, %944 ]
  %949 = phi double [ %958, %951 ], [ %946, %944 ]
  %950 = icmp slt i64 %948, 0
  br i1 %950, label %951, label %961

951:                                              ; preds = %947
  %952 = icmp samesign ult i64 %948, -22
  %953 = mul i64 %948, -4294967296
  %954 = ashr exact i64 %953, 32
  %955 = select i1 %952, i64 22, i64 %954
  %956 = getelementptr inbounds [23 x double], ptr @NUMF_EL1_POW10, i64 0, i64 %955
  %957 = load double, ptr %956, align 8, !tbaa !19
  %958 = fdiv double %949, %957
  %959 = add i64 %955, %948
  %960 = fcmp oeq double %958, 0.000000e+00
  br i1 %960, label %961, label %947

961:                                              ; preds = %951, %947
  %962 = phi double [ %958, %951 ], [ %949, %947 ]
  %963 = bitcast double %962 to i64
  br label %964

964:                                              ; preds = %1024, %961
  %965 = phi i64 [ %963, %961 ], [ %1025, %1024 ]
  %966 = icmp eq i64 %965, 0
  br i1 %966, label %967, label %970

967:                                              ; preds = %964
  %968 = call fastcc i32 @stk_cmp(ptr noundef %6, i64 noundef 1, i64 noundef -1075)
  %969 = icmp sgt i32 %968, 0
  br i1 %969, label %1024, label %1026

970:                                              ; preds = %964
  %971 = icmp ugt i64 %965, 9218868437227405311
  br i1 %971, label %972, label %975

972:                                              ; preds = %970
  %973 = call fastcc i32 @stk_cmp(ptr noundef %6, i64 noundef 18014398509481983, i64 noundef 970)
  %974 = icmp slt i32 %973, 0
  br i1 %974, label %1024, label %1026

975:                                              ; preds = %970
  %976 = lshr i64 %965, 52
  %977 = icmp samesign ult i64 %965, 4503599627370496
  %978 = and i64 %965, 4503599627370495
  %979 = or disjoint i64 %978, 4503599627370496
  %980 = select i1 %977, i64 %965, i64 %979
  %981 = add nsw i64 %976, -1075
  %982 = select i1 %977, i64 -1074, i64 %981
  %983 = call fastcc i32 @stk_cmp(ptr noundef %6, i64 noundef %980, i64 noundef %982)
  %984 = icmp eq i32 %983, 0
  br i1 %984, label %1026, label %985

985:                                              ; preds = %975
  %986 = icmp sgt i32 %983, 0
  br i1 %986, label %987, label %1000

987:                                              ; preds = %985
  %988 = shl nuw nsw i64 %980, 1
  %989 = or disjoint i64 %988, 1
  %990 = add nsw i64 %982, -1
  %991 = call fastcc i32 @stk_cmp(ptr noundef %6, i64 noundef %989, i64 noundef %990)
  %992 = icmp slt i32 %991, 0
  br i1 %992, label %1026, label %993

993:                                              ; preds = %987
  %994 = icmp eq i32 %991, 0
  br i1 %994, label %995, label %998

995:                                              ; preds = %993
  %996 = and i64 %980, 1
  %997 = add nuw nsw i64 %996, %965
  br label %1026

998:                                              ; preds = %993
  %999 = add nuw nsw i64 %965, 1
  br label %1024

1000:                                             ; preds = %985
  %1001 = icmp samesign ugt i64 %980, 4503599627370496
  %1002 = or i1 %977, %1001
  br i1 %1002, label %1003, label %1007

1003:                                             ; preds = %1000
  %1004 = shl nuw nsw i64 %980, 1
  %1005 = add nsw i64 %1004, -1
  %1006 = add nsw i64 %982, -1
  br label %1012

1007:                                             ; preds = %1000
  %1008 = icmp eq i64 %976, 1
  %1009 = add nsw i64 %976, -1077
  %1010 = select i1 %1008, i64 9007199254740991, i64 18014398509481983
  %1011 = select i1 %1008, i64 -1075, i64 %1009
  br label %1012

1012:                                             ; preds = %1007, %1003
  %1013 = phi i64 [ %1005, %1003 ], [ %1010, %1007 ]
  %1014 = phi i64 [ %1006, %1003 ], [ %1011, %1007 ]
  %1015 = call fastcc i32 @stk_cmp(ptr noundef %6, i64 noundef %1013, i64 noundef %1014)
  %1016 = icmp sgt i32 %1015, 0
  br i1 %1016, label %1026, label %1017

1017:                                             ; preds = %1012
  %1018 = icmp eq i32 %1015, 0
  br i1 %1018, label %1019, label %1022

1019:                                             ; preds = %1017
  %1020 = and i64 %980, 1
  %1021 = sub nuw nsw i64 %965, %1020
  br label %1026

1022:                                             ; preds = %1017
  %1023 = add nsw i64 %965, -1
  br label %1024

1024:                                             ; preds = %1022, %998, %972, %967
  %1025 = phi i64 [ 1, %967 ], [ 9218868437227405311, %972 ], [ %999, %998 ], [ %1023, %1022 ]
  br label %964

1026:                                             ; preds = %1012, %987, %975, %972, %967, %1019, %995
  %1027 = phi i64 [ %1021, %1019 ], [ %997, %995 ], [ 0, %967 ], [ 9218868437227405312, %972 ], [ %965, %1012 ], [ %965, %987 ], [ %965, %975 ]
  %1028 = bitcast i64 %1027 to double
  %1029 = fneg double %1028
  %1030 = select i1 %8, double %1029, double %1028
  call void @llvm.lifetime.end.p0(i64 1568, ptr nonnull %6) #11
  br label %1031

1031:                                             ; preds = %186, %300, %304, %1026
  %1032 = phi double [ %187, %186 ], [ %305, %304 ], [ %1030, %1026 ], [ %301, %300 ]
  call void @llvm.lifetime.end.p0(i64 768, ptr nonnull %5) #11
  store double %1032, ptr %2, align 8, !tbaa !19
  br label %1033

1033:                                             ; preds = %1031, %91, %78, %46, %30, %11
  %1034 = phi i32 [ 0, %11 ], [ 0, %46 ], [ 0, %78 ], [ 0, %91 ], [ 1, %1031 ], [ 0, %30 ]
  ret i32 %1034
}

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(none)
declare <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8>, <16 x i8>) #6

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(none)
declare <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16>, <8 x i16>) #6

; Function Attrs: mustprogress nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.ctlz.i64(i64, i1 immarg) #7

; Function Attrs: nofree norecurse nosync nounwind sspstrong memory(argmem: readwrite) uwtable
define internal fastcc void @stk_mul_u64(ptr noundef nonnull captures(none) %0, i64 noundef %1) unnamed_addr #8 align 64 {
  %3 = getelementptr inbounds nuw i8, ptr %0, i64 768
  %4 = load i32, ptr %3, align 8, !tbaa !48
  %5 = icmp sgt i32 %4, 0
  br i1 %5, label %6, label %82

6:                                                ; preds = %2
  %7 = zext i64 %1 to i128
  %8 = zext nneg i32 %4 to i64
  %9 = and i64 %8, 3
  %10 = icmp ult i32 %4, 4
  br i1 %10, label %15, label %11

11:                                               ; preds = %6
  %12 = and i64 %8, 2147483644
  br label %44

13:                                               ; preds = %44
  %14 = trunc nuw i128 %78 to i64
  br label %15

15:                                               ; preds = %13, %6
  %16 = phi i128 [ poison, %6 ], [ %76, %13 ]
  %17 = phi i64 [ poison, %6 ], [ %14, %13 ]
  %18 = phi i64 [ 0, %6 ], [ %79, %13 ]
  %19 = phi i128 [ 0, %6 ], [ %78, %13 ]
  %20 = icmp eq i64 %9, 0
  br i1 %20, label %37, label %21

21:                                               ; preds = %15, %21
  %22 = phi i64 [ %32, %21 ], [ %18, %15 ]
  %23 = phi i128 [ %31, %21 ], [ %19, %15 ]
  %24 = phi i64 [ %33, %21 ], [ 0, %15 ]
  %25 = getelementptr inbounds nuw [96 x i64], ptr %0, i64 0, i64 %22
  %26 = load i64, ptr %25, align 8, !tbaa !6
  %27 = zext i64 %26 to i128
  %28 = mul nuw i128 %27, %7
  %29 = add nuw i128 %28, %23
  %30 = trunc i128 %29 to i64
  store i64 %30, ptr %25, align 8, !tbaa !6
  %31 = lshr i128 %29, 64
  %32 = add nuw nsw i64 %22, 1
  %33 = add i64 %24, 1
  %34 = icmp eq i64 %33, %9
  br i1 %34, label %35, label %21, !llvm.loop !57

35:                                               ; preds = %21
  %36 = trunc nuw i128 %31 to i64
  br label %37

37:                                               ; preds = %15, %35
  %38 = phi i128 [ %16, %15 ], [ %29, %35 ]
  %39 = phi i64 [ %17, %15 ], [ %36, %35 ]
  %40 = icmp ult i128 %38, 18446744073709551616
  br i1 %40, label %82, label %41

41:                                               ; preds = %37
  %42 = getelementptr inbounds nuw [96 x i64], ptr %0, i64 0, i64 %8
  store i64 %39, ptr %42, align 8, !tbaa !6
  %43 = add nuw i32 %4, 1
  store i32 %43, ptr %3, align 8, !tbaa !48
  br label %82

44:                                               ; preds = %44, %11
  %45 = phi i64 [ 0, %11 ], [ %79, %44 ]
  %46 = phi i128 [ 0, %11 ], [ %78, %44 ]
  %47 = phi i64 [ 0, %11 ], [ %80, %44 ]
  %48 = getelementptr inbounds nuw [96 x i64], ptr %0, i64 0, i64 %45
  %49 = load i64, ptr %48, align 8, !tbaa !6
  %50 = zext i64 %49 to i128
  %51 = mul nuw i128 %50, %7
  %52 = add nuw i128 %51, %46
  %53 = trunc i128 %52 to i64
  store i64 %53, ptr %48, align 8, !tbaa !6
  %54 = lshr i128 %52, 64
  %55 = or disjoint i64 %45, 1
  %56 = getelementptr inbounds nuw [96 x i64], ptr %0, i64 0, i64 %55
  %57 = load i64, ptr %56, align 8, !tbaa !6
  %58 = zext i64 %57 to i128
  %59 = mul nuw i128 %58, %7
  %60 = add nuw i128 %59, %54
  %61 = trunc i128 %60 to i64
  store i64 %61, ptr %56, align 8, !tbaa !6
  %62 = lshr i128 %60, 64
  %63 = or disjoint i64 %45, 2
  %64 = getelementptr inbounds nuw [96 x i64], ptr %0, i64 0, i64 %63
  %65 = load i64, ptr %64, align 8, !tbaa !6
  %66 = zext i64 %65 to i128
  %67 = mul nuw i128 %66, %7
  %68 = add nuw i128 %67, %62
  %69 = trunc i128 %68 to i64
  store i64 %69, ptr %64, align 8, !tbaa !6
  %70 = lshr i128 %68, 64
  %71 = or disjoint i64 %45, 3
  %72 = getelementptr inbounds nuw [96 x i64], ptr %0, i64 0, i64 %71
  %73 = load i64, ptr %72, align 8, !tbaa !6
  %74 = zext i64 %73 to i128
  %75 = mul nuw i128 %74, %7
  %76 = add nuw i128 %75, %70
  %77 = trunc i128 %76 to i64
  store i64 %77, ptr %72, align 8, !tbaa !6
  %78 = lshr i128 %76, 64
  %79 = add nuw nsw i64 %45, 4
  %80 = add i64 %47, 4
  %81 = icmp eq i64 %80, %12
  br i1 %81, label %13, label %44, !llvm.loop !45

82:                                               ; preds = %2, %37, %41
  ret void
}

; Function Attrs: nofree norecurse nounwind sspstrong memory(argmem: readwrite) uwtable
define internal fastcc range(i32 -1, 2) i32 @stk_cmp(ptr noundef nonnull readonly captures(none) %0, i64 noundef range(i64 -1, 18014398509481984) %1, i64 noundef range(i64 -1077, 972) %2) unnamed_addr #5 align 64 {
  %4 = alloca %struct.StkBn, align 8
  %5 = alloca %struct.StkBn, align 8
  call void @llvm.lifetime.start.p0(i64 776, ptr nonnull %4) #11
  call void @llvm.lifetime.start.p0(i64 776, ptr nonnull %5) #11
  %6 = getelementptr inbounds nuw i8, ptr %0, i64 1560
  %7 = load i32, ptr %6, align 8, !tbaa !40
  %8 = icmp eq i32 %7, 0
  br i1 %8, label %357, label %9

9:                                                ; preds = %3
  %10 = getelementptr inbounds nuw i8, ptr %0, i64 1544
  %11 = load i32, ptr %10, align 8, !tbaa !48
  %12 = getelementptr inbounds nuw i8, ptr %5, i64 768
  store i32 %11, ptr %12, align 8, !tbaa !48
  %13 = icmp eq i32 %11, 0
  br i1 %13, label %332, label %14

14:                                               ; preds = %9
  %15 = getelementptr inbounds nuw i8, ptr %0, i64 776
  %16 = sext i32 %11 to i64
  %17 = shl nsw i64 %16, 3
  %18 = call ptr @__memcpy_chk(ptr noundef nonnull %5, ptr noundef nonnull readonly %15, i64 noundef range(i64 -17179869184, 17179869177) %17, i64 noundef 776) #11, !alias.scope !58
  %19 = load i32, ptr %12, align 8, !tbaa !48
  %20 = icmp sgt i32 %19, 0
  br i1 %20, label %21, label %97

21:                                               ; preds = %14
  %22 = zext i64 %1 to i128
  %23 = zext nneg i32 %19 to i64
  %24 = and i64 %23, 3
  %25 = icmp ult i32 %19, 4
  br i1 %25, label %30, label %26

26:                                               ; preds = %21
  %27 = and i64 %23, 2147483644
  br label %59

28:                                               ; preds = %59
  %29 = trunc nuw i128 %93 to i64
  br label %30

30:                                               ; preds = %28, %21
  %31 = phi i128 [ poison, %21 ], [ %91, %28 ]
  %32 = phi i64 [ poison, %21 ], [ %29, %28 ]
  %33 = phi i64 [ 0, %21 ], [ %94, %28 ]
  %34 = phi i128 [ 0, %21 ], [ %93, %28 ]
  %35 = icmp eq i64 %24, 0
  br i1 %35, label %52, label %36

36:                                               ; preds = %30, %36
  %37 = phi i64 [ %47, %36 ], [ %33, %30 ]
  %38 = phi i128 [ %46, %36 ], [ %34, %30 ]
  %39 = phi i64 [ %48, %36 ], [ 0, %30 ]
  %40 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %37
  %41 = load i64, ptr %40, align 8, !tbaa !6
  %42 = zext i64 %41 to i128
  %43 = mul nuw i128 %42, %22
  %44 = add nuw i128 %43, %38
  %45 = trunc i128 %44 to i64
  store i64 %45, ptr %40, align 8, !tbaa !6
  %46 = lshr i128 %44, 64
  %47 = add nuw nsw i64 %37, 1
  %48 = add i64 %39, 1
  %49 = icmp eq i64 %48, %24
  br i1 %49, label %50, label %36, !llvm.loop !62

50:                                               ; preds = %36
  %51 = trunc nuw i128 %46 to i64
  br label %52

52:                                               ; preds = %30, %50
  %53 = phi i128 [ %31, %30 ], [ %44, %50 ]
  %54 = phi i64 [ %32, %30 ], [ %51, %50 ]
  %55 = icmp ult i128 %53, 18446744073709551616
  br i1 %55, label %97, label %56

56:                                               ; preds = %52
  %57 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %23
  store i64 %54, ptr %57, align 8, !tbaa !6
  %58 = add nuw i32 %19, 1
  br label %97

59:                                               ; preds = %59, %26
  %60 = phi i64 [ 0, %26 ], [ %94, %59 ]
  %61 = phi i128 [ 0, %26 ], [ %93, %59 ]
  %62 = phi i64 [ 0, %26 ], [ %95, %59 ]
  %63 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %60
  %64 = load i64, ptr %63, align 8, !tbaa !6
  %65 = zext i64 %64 to i128
  %66 = mul nuw i128 %65, %22
  %67 = add nuw i128 %66, %61
  %68 = trunc i128 %67 to i64
  store i64 %68, ptr %63, align 8, !tbaa !6
  %69 = lshr i128 %67, 64
  %70 = or disjoint i64 %60, 1
  %71 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %70
  %72 = load i64, ptr %71, align 8, !tbaa !6
  %73 = zext i64 %72 to i128
  %74 = mul nuw i128 %73, %22
  %75 = add nuw i128 %74, %69
  %76 = trunc i128 %75 to i64
  store i64 %76, ptr %71, align 8, !tbaa !6
  %77 = lshr i128 %75, 64
  %78 = or disjoint i64 %60, 2
  %79 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %78
  %80 = load i64, ptr %79, align 8, !tbaa !6
  %81 = zext i64 %80 to i128
  %82 = mul nuw i128 %81, %22
  %83 = add nuw i128 %82, %77
  %84 = trunc i128 %83 to i64
  store i64 %84, ptr %79, align 8, !tbaa !6
  %85 = lshr i128 %83, 64
  %86 = or disjoint i64 %60, 3
  %87 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %86
  %88 = load i64, ptr %87, align 8, !tbaa !6
  %89 = zext i64 %88 to i128
  %90 = mul nuw i128 %89, %22
  %91 = add nuw i128 %90, %85
  %92 = trunc i128 %91 to i64
  store i64 %92, ptr %87, align 8, !tbaa !6
  %93 = lshr i128 %91, 64
  %94 = add nuw nsw i64 %60, 4
  %95 = add i64 %62, 4
  %96 = icmp eq i64 %95, %27
  br i1 %96, label %28, label %59, !llvm.loop !45

97:                                               ; preds = %14, %52, %56
  %98 = phi i32 [ %19, %14 ], [ %19, %52 ], [ %58, %56 ]
  %99 = getelementptr inbounds nuw i8, ptr %0, i64 1552
  %100 = load i64, ptr %99, align 8, !tbaa !43
  %101 = sub i64 %2, %100
  %102 = trunc i64 %101 to i32
  %103 = icmp eq i32 %102, 0
  br i1 %103, label %332, label %104

104:                                              ; preds = %97
  %105 = icmp eq i32 %98, 0
  br i1 %105, label %332, label %106

106:                                              ; preds = %104
  %107 = lshr i32 %102, 6
  %108 = and i32 %102, 63
  %109 = icmp ne i32 %108, 0
  %110 = icmp sgt i32 %98, 0
  %111 = and i1 %109, %110
  br i1 %111, label %112, label %174

112:                                              ; preds = %106
  %113 = and i64 %101, 63
  %114 = sub nuw nsw i32 64, %108
  %115 = zext nneg i32 %114 to i64
  %116 = zext nneg i32 %98 to i64
  %117 = and i64 %116, 3
  %118 = icmp ult i32 %98, 4
  br i1 %118, label %121, label %119

119:                                              ; preds = %112
  %120 = and i64 %116, 2147483644
  br label %141

121:                                              ; preds = %141, %112
  %122 = phi i64 [ poison, %112 ], [ %167, %141 ]
  %123 = phi i64 [ 0, %112 ], [ %168, %141 ]
  %124 = phi i64 [ 0, %112 ], [ %167, %141 ]
  %125 = icmp eq i64 %117, 0
  br i1 %125, label %138, label %126

126:                                              ; preds = %121, %126
  %127 = phi i64 [ %135, %126 ], [ %123, %121 ]
  %128 = phi i64 [ %134, %126 ], [ %124, %121 ]
  %129 = phi i64 [ %136, %126 ], [ 0, %121 ]
  %130 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %127
  %131 = load i64, ptr %130, align 8, !tbaa !6
  %132 = shl i64 %131, %113
  %133 = or i64 %132, %128
  store i64 %133, ptr %130, align 8, !tbaa !6
  %134 = lshr i64 %131, %115
  %135 = add nuw nsw i64 %127, 1
  %136 = add i64 %129, 1
  %137 = icmp eq i64 %136, %117
  br i1 %137, label %138, label %126, !llvm.loop !63

138:                                              ; preds = %126, %121
  %139 = phi i64 [ %122, %121 ], [ %134, %126 ]
  %140 = icmp eq i64 %139, 0
  br i1 %140, label %174, label %171

141:                                              ; preds = %141, %119
  %142 = phi i64 [ 0, %119 ], [ %168, %141 ]
  %143 = phi i64 [ 0, %119 ], [ %167, %141 ]
  %144 = phi i64 [ 0, %119 ], [ %169, %141 ]
  %145 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %142
  %146 = load i64, ptr %145, align 8, !tbaa !6
  %147 = shl i64 %146, %113
  %148 = or i64 %147, %143
  store i64 %148, ptr %145, align 8, !tbaa !6
  %149 = lshr i64 %146, %115
  %150 = or disjoint i64 %142, 1
  %151 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %150
  %152 = load i64, ptr %151, align 8, !tbaa !6
  %153 = shl i64 %152, %113
  %154 = or i64 %153, %149
  store i64 %154, ptr %151, align 8, !tbaa !6
  %155 = lshr i64 %152, %115
  %156 = or disjoint i64 %142, 2
  %157 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %156
  %158 = load i64, ptr %157, align 8, !tbaa !6
  %159 = shl i64 %158, %113
  %160 = or i64 %159, %155
  store i64 %160, ptr %157, align 8, !tbaa !6
  %161 = lshr i64 %158, %115
  %162 = or disjoint i64 %142, 3
  %163 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %162
  %164 = load i64, ptr %163, align 8, !tbaa !6
  %165 = shl i64 %164, %113
  %166 = or i64 %165, %161
  store i64 %166, ptr %163, align 8, !tbaa !6
  %167 = lshr i64 %164, %115
  %168 = add nuw nsw i64 %142, 4
  %169 = add i64 %144, 4
  %170 = icmp eq i64 %169, %120
  br i1 %170, label %121, label %141, !llvm.loop !64

171:                                              ; preds = %138
  %172 = add nuw i32 %98, 1
  %173 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %116
  store i64 %139, ptr %173, align 8, !tbaa !6
  br label %174

174:                                              ; preds = %171, %138, %106
  %175 = phi i32 [ %98, %138 ], [ %172, %171 ], [ %98, %106 ]
  %176 = icmp ult i32 %102, 64
  br i1 %176, label %332, label %177

177:                                              ; preds = %174
  %178 = add i32 %175, -1
  %179 = icmp sgt i32 %178, -1
  br i1 %179, label %180, label %328

180:                                              ; preds = %177
  %181 = zext nneg i32 %178 to i64
  %182 = zext i32 %175 to i64
  %183 = icmp ult i32 %175, 4
  br i1 %183, label %248, label %184

184:                                              ; preds = %180
  %185 = add i32 %175, %107
  %186 = add i32 %185, -1
  %187 = icmp sgt i32 %107, %186
  br i1 %187, label %248, label %188

188:                                              ; preds = %184
  %189 = add i32 %175, %107
  %190 = add i32 %189, -1
  %191 = sext i32 %190 to i64
  %192 = sub nsw i64 %181, %191
  %193 = and i64 %192, 2305843009213693936
  %194 = icmp eq i64 %193, 0
  br i1 %194, label %248, label %195

195:                                              ; preds = %188
  %196 = icmp ult i32 %175, 16
  br i1 %196, label %228, label %197

197:                                              ; preds = %195
  %198 = and i64 %182, 4294967280
  br label %199

199:                                              ; preds = %199, %197
  %200 = phi i64 [ 0, %197 ], [ %220, %199 ]
  %201 = sub i64 %181, %200
  %202 = trunc i64 %200 to i32
  %203 = sub i32 %178, %202
  %204 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %201
  %205 = getelementptr inbounds i8, ptr %204, i64 -24
  %206 = getelementptr inbounds i8, ptr %204, i64 -56
  %207 = getelementptr inbounds i8, ptr %204, i64 -88
  %208 = getelementptr inbounds i8, ptr %204, i64 -120
  %209 = load <4 x i64>, ptr %205, align 8, !tbaa !6
  %210 = load <4 x i64>, ptr %206, align 8, !tbaa !6
  %211 = load <4 x i64>, ptr %207, align 8, !tbaa !6
  %212 = load <4 x i64>, ptr %208, align 8, !tbaa !6
  %213 = add i32 %107, %203
  %214 = sext i32 %213 to i64
  %215 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %214
  %216 = getelementptr inbounds i8, ptr %215, i64 -24
  %217 = getelementptr inbounds i8, ptr %215, i64 -56
  %218 = getelementptr inbounds i8, ptr %215, i64 -88
  %219 = getelementptr inbounds i8, ptr %215, i64 -120
  store <4 x i64> %209, ptr %216, align 8, !tbaa !6
  store <4 x i64> %210, ptr %217, align 8, !tbaa !6
  store <4 x i64> %211, ptr %218, align 8, !tbaa !6
  store <4 x i64> %212, ptr %219, align 8, !tbaa !6
  %220 = add nuw i64 %200, 16
  %221 = icmp eq i64 %220, %198
  br i1 %221, label %222, label %199, !llvm.loop !65

222:                                              ; preds = %199
  %223 = icmp eq i64 %198, %182
  br i1 %223, label %328, label %224

224:                                              ; preds = %222
  %225 = sub nsw i64 %181, %198
  %226 = and i64 %182, 12
  %227 = icmp eq i64 %226, 0
  br i1 %227, label %248, label %228

228:                                              ; preds = %224, %195
  %229 = phi i64 [ %198, %224 ], [ 0, %195 ]
  %230 = and i64 %182, 4294967292
  %231 = sub nsw i64 %181, %230
  %232 = getelementptr i8, ptr %5, i64 -24
  %233 = getelementptr i8, ptr %5, i64 -24
  br label %234

234:                                              ; preds = %234, %228
  %235 = phi i64 [ %229, %228 ], [ %244, %234 ]
  %236 = sub i64 %181, %235
  %237 = trunc i64 %235 to i32
  %238 = sub i32 %178, %237
  %239 = getelementptr [96 x i64], ptr %232, i64 0, i64 %236
  %240 = load <4 x i64>, ptr %239, align 8, !tbaa !6
  %241 = add i32 %107, %238
  %242 = sext i32 %241 to i64
  %243 = getelementptr [96 x i64], ptr %233, i64 0, i64 %242
  store <4 x i64> %240, ptr %243, align 8, !tbaa !6
  %244 = add nuw i64 %235, 4
  %245 = icmp eq i64 %244, %230
  br i1 %245, label %246, label %234, !llvm.loop !68

246:                                              ; preds = %234
  %247 = icmp eq i64 %230, %182
  br i1 %247, label %328, label %248

248:                                              ; preds = %224, %246, %188, %184, %180
  %249 = phi i64 [ %181, %180 ], [ %181, %184 ], [ %181, %188 ], [ %225, %224 ], [ %231, %246 ]
  %250 = add nsw i64 %249, 1
  %251 = and i64 %250, 7
  %252 = and i64 %249, 7
  %253 = icmp eq i64 %252, 7
  br i1 %253, label %266, label %254

254:                                              ; preds = %248, %254
  %255 = phi i64 [ %263, %254 ], [ %249, %248 ]
  %256 = phi i64 [ %264, %254 ], [ 0, %248 ]
  %257 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %255
  %258 = load i64, ptr %257, align 8, !tbaa !6
  %259 = trunc i64 %255 to i32
  %260 = add i32 %107, %259
  %261 = sext i32 %260 to i64
  %262 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %261
  store i64 %258, ptr %262, align 8, !tbaa !6
  %263 = add nsw i64 %255, -1
  %264 = add i64 %256, 1
  %265 = icmp eq i64 %264, %251
  br i1 %265, label %266, label %254, !llvm.loop !69

266:                                              ; preds = %254, %248
  %267 = phi i64 [ %249, %248 ], [ %263, %254 ]
  %268 = icmp ult i64 %249, 7
  br i1 %268, label %328, label %269

269:                                              ; preds = %266, %269
  %270 = phi i64 [ %326, %269 ], [ %267, %266 ]
  %271 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %270
  %272 = load i64, ptr %271, align 8, !tbaa !6
  %273 = trunc i64 %270 to i32
  %274 = add i32 %107, %273
  %275 = sext i32 %274 to i64
  %276 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %275
  store i64 %272, ptr %276, align 8, !tbaa !6
  %277 = add nsw i64 %270, -1
  %278 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %277
  %279 = load i64, ptr %278, align 8, !tbaa !6
  %280 = trunc i64 %277 to i32
  %281 = add i32 %107, %280
  %282 = sext i32 %281 to i64
  %283 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %282
  store i64 %279, ptr %283, align 8, !tbaa !6
  %284 = add nsw i64 %270, -2
  %285 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %284
  %286 = load i64, ptr %285, align 8, !tbaa !6
  %287 = trunc i64 %284 to i32
  %288 = add i32 %107, %287
  %289 = sext i32 %288 to i64
  %290 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %289
  store i64 %286, ptr %290, align 8, !tbaa !6
  %291 = add nsw i64 %270, -3
  %292 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %291
  %293 = load i64, ptr %292, align 8, !tbaa !6
  %294 = trunc i64 %291 to i32
  %295 = add i32 %107, %294
  %296 = sext i32 %295 to i64
  %297 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %296
  store i64 %293, ptr %297, align 8, !tbaa !6
  %298 = add nsw i64 %270, -4
  %299 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %298
  %300 = load i64, ptr %299, align 8, !tbaa !6
  %301 = trunc i64 %298 to i32
  %302 = add i32 %107, %301
  %303 = sext i32 %302 to i64
  %304 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %303
  store i64 %300, ptr %304, align 8, !tbaa !6
  %305 = add nsw i64 %270, -5
  %306 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %305
  %307 = load i64, ptr %306, align 8, !tbaa !6
  %308 = trunc i64 %305 to i32
  %309 = add i32 %107, %308
  %310 = sext i32 %309 to i64
  %311 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %310
  store i64 %307, ptr %311, align 8, !tbaa !6
  %312 = add nsw i64 %270, -6
  %313 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %312
  %314 = load i64, ptr %313, align 8, !tbaa !6
  %315 = trunc i64 %312 to i32
  %316 = add i32 %107, %315
  %317 = sext i32 %316 to i64
  %318 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %317
  store i64 %314, ptr %318, align 8, !tbaa !6
  %319 = add nsw i64 %270, -7
  %320 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %319
  %321 = load i64, ptr %320, align 8, !tbaa !6
  %322 = trunc i64 %319 to i32
  %323 = add i32 %107, %322
  %324 = sext i32 %323 to i64
  %325 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %324
  store i64 %321, ptr %325, align 8, !tbaa !6
  %326 = add nsw i64 %270, -8
  %327 = icmp eq i64 %319, 0
  br i1 %327, label %328, label %269, !llvm.loop !70

328:                                              ; preds = %266, %269, %222, %246, %177
  %329 = lshr i64 %101, 3
  %330 = and i64 %329, 536870904
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 8 dereferenceable(1) %5, i8 0, i64 %330, i1 false), !tbaa !6
  %331 = add i32 %175, %107
  br label %332

332:                                              ; preds = %9, %97, %104, %174, %328
  %333 = phi i32 [ %98, %97 ], [ 0, %104 ], [ %175, %174 ], [ %331, %328 ], [ 0, %9 ]
  %334 = getelementptr inbounds nuw i8, ptr %0, i64 768
  %335 = load i32, ptr %334, align 8, !tbaa !48
  %336 = icmp eq i32 %335, %333
  br i1 %336, label %337, label %339

337:                                              ; preds = %332
  %338 = zext i32 %333 to i64
  br label %342

339:                                              ; preds = %332
  %340 = icmp slt i32 %335, %333
  %341 = select i1 %340, i32 -1, i32 1
  br label %944

342:                                              ; preds = %347, %337
  %343 = phi i64 [ %338, %337 ], [ %344, %347 ]
  %344 = add nsw i64 %343, -1
  %345 = and i64 %344, 2147483648
  %346 = icmp eq i64 %345, 0
  br i1 %346, label %347, label %944

347:                                              ; preds = %342
  %348 = and i64 %344, 2147483647
  %349 = getelementptr inbounds nuw [96 x i64], ptr %0, i64 0, i64 %348
  %350 = load i64, ptr %349, align 8, !tbaa !6
  %351 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %348
  %352 = load i64, ptr %351, align 8, !tbaa !6
  %353 = icmp eq i64 %350, %352
  br i1 %353, label %342, label %354, !llvm.loop !71

354:                                              ; preds = %347
  %355 = icmp ult i64 %350, %352
  %356 = select i1 %355, i32 -1, i32 1
  br label %944

357:                                              ; preds = %3
  %358 = getelementptr inbounds nuw i8, ptr %0, i64 768
  %359 = load i32, ptr %358, align 8, !tbaa !48
  %360 = getelementptr inbounds nuw i8, ptr %4, i64 768
  store i32 %359, ptr %360, align 8, !tbaa !48
  %361 = icmp eq i32 %359, 0
  br i1 %361, label %366, label %362

362:                                              ; preds = %357
  %363 = sext i32 %359 to i64
  %364 = shl nsw i64 %363, 3
  %365 = call ptr @__memcpy_chk(ptr noundef nonnull %4, ptr noundef nonnull readonly %0, i64 noundef range(i64 -17179869184, 17179869177) %364, i64 noundef 776) #11, !alias.scope !72
  br label %366

366:                                              ; preds = %357, %362
  %367 = icmp slt i64 %2, 0
  br i1 %367, label %368, label %600

368:                                              ; preds = %366
  %369 = trunc i64 %2 to i32
  %370 = sub i32 0, %369
  %371 = load i32, ptr %360, align 8, !tbaa !48
  %372 = icmp eq i32 %371, 0
  br i1 %372, label %600, label %373

373:                                              ; preds = %368
  %374 = lshr i32 %370, 6
  %375 = and i32 %370, 63
  %376 = icmp ne i32 %375, 0
  %377 = icmp sgt i32 %371, 0
  %378 = and i1 %376, %377
  br i1 %378, label %379, label %441

379:                                              ; preds = %373
  %380 = zext nneg i32 %375 to i64
  %381 = sub nuw nsw i32 64, %375
  %382 = zext nneg i32 %381 to i64
  %383 = zext nneg i32 %371 to i64
  %384 = and i64 %383, 3
  %385 = icmp ult i32 %371, 4
  br i1 %385, label %388, label %386

386:                                              ; preds = %379
  %387 = and i64 %383, 2147483644
  br label %408

388:                                              ; preds = %408, %379
  %389 = phi i64 [ poison, %379 ], [ %434, %408 ]
  %390 = phi i64 [ 0, %379 ], [ %435, %408 ]
  %391 = phi i64 [ 0, %379 ], [ %434, %408 ]
  %392 = icmp eq i64 %384, 0
  br i1 %392, label %405, label %393

393:                                              ; preds = %388, %393
  %394 = phi i64 [ %402, %393 ], [ %390, %388 ]
  %395 = phi i64 [ %401, %393 ], [ %391, %388 ]
  %396 = phi i64 [ %403, %393 ], [ 0, %388 ]
  %397 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %394
  %398 = load i64, ptr %397, align 8, !tbaa !6
  %399 = shl i64 %398, %380
  %400 = or i64 %399, %395
  store i64 %400, ptr %397, align 8, !tbaa !6
  %401 = lshr i64 %398, %382
  %402 = add nuw nsw i64 %394, 1
  %403 = add i64 %396, 1
  %404 = icmp eq i64 %403, %384
  br i1 %404, label %405, label %393, !llvm.loop !76

405:                                              ; preds = %393, %388
  %406 = phi i64 [ %389, %388 ], [ %401, %393 ]
  %407 = icmp eq i64 %406, 0
  br i1 %407, label %441, label %438

408:                                              ; preds = %408, %386
  %409 = phi i64 [ 0, %386 ], [ %435, %408 ]
  %410 = phi i64 [ 0, %386 ], [ %434, %408 ]
  %411 = phi i64 [ 0, %386 ], [ %436, %408 ]
  %412 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %409
  %413 = load i64, ptr %412, align 8, !tbaa !6
  %414 = shl i64 %413, %380
  %415 = or i64 %414, %410
  store i64 %415, ptr %412, align 8, !tbaa !6
  %416 = lshr i64 %413, %382
  %417 = or disjoint i64 %409, 1
  %418 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %417
  %419 = load i64, ptr %418, align 8, !tbaa !6
  %420 = shl i64 %419, %380
  %421 = or i64 %420, %416
  store i64 %421, ptr %418, align 8, !tbaa !6
  %422 = lshr i64 %419, %382
  %423 = or disjoint i64 %409, 2
  %424 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %423
  %425 = load i64, ptr %424, align 8, !tbaa !6
  %426 = shl i64 %425, %380
  %427 = or i64 %426, %422
  store i64 %427, ptr %424, align 8, !tbaa !6
  %428 = lshr i64 %425, %382
  %429 = or disjoint i64 %409, 3
  %430 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %429
  %431 = load i64, ptr %430, align 8, !tbaa !6
  %432 = shl i64 %431, %380
  %433 = or i64 %432, %428
  store i64 %433, ptr %430, align 8, !tbaa !6
  %434 = lshr i64 %431, %382
  %435 = add nuw nsw i64 %409, 4
  %436 = add i64 %411, 4
  %437 = icmp eq i64 %436, %387
  br i1 %437, label %388, label %408, !llvm.loop !64

438:                                              ; preds = %405
  %439 = add nuw i32 %371, 1
  store i32 %439, ptr %360, align 8, !tbaa !48
  %440 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %383
  store i64 %406, ptr %440, align 8, !tbaa !6
  br label %441

441:                                              ; preds = %438, %405, %373
  %442 = phi i32 [ %371, %405 ], [ %439, %438 ], [ %371, %373 ]
  %443 = icmp samesign ult i32 %370, 64
  br i1 %443, label %600, label %444

444:                                              ; preds = %441
  %445 = add i32 %442, -1
  %446 = icmp sgt i32 %445, -1
  br i1 %446, label %447, label %595

447:                                              ; preds = %444
  %448 = zext nneg i32 %445 to i64
  %449 = zext i32 %442 to i64
  %450 = icmp ult i32 %442, 4
  br i1 %450, label %515, label %451

451:                                              ; preds = %447
  %452 = add i32 %442, %374
  %453 = add i32 %452, -1
  %454 = icmp sgt i32 %374, %453
  br i1 %454, label %515, label %455

455:                                              ; preds = %451
  %456 = add i32 %442, %374
  %457 = add i32 %456, -1
  %458 = sext i32 %457 to i64
  %459 = sub nsw i64 %448, %458
  %460 = and i64 %459, 2305843009213693936
  %461 = icmp eq i64 %460, 0
  br i1 %461, label %515, label %462

462:                                              ; preds = %455
  %463 = icmp ult i32 %442, 16
  br i1 %463, label %495, label %464

464:                                              ; preds = %462
  %465 = and i64 %449, 4294967280
  br label %466

466:                                              ; preds = %466, %464
  %467 = phi i64 [ 0, %464 ], [ %487, %466 ]
  %468 = sub i64 %448, %467
  %469 = trunc i64 %467 to i32
  %470 = sub i32 %445, %469
  %471 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %468
  %472 = getelementptr inbounds i8, ptr %471, i64 -24
  %473 = getelementptr inbounds i8, ptr %471, i64 -56
  %474 = getelementptr inbounds i8, ptr %471, i64 -88
  %475 = getelementptr inbounds i8, ptr %471, i64 -120
  %476 = load <4 x i64>, ptr %472, align 8, !tbaa !6
  %477 = load <4 x i64>, ptr %473, align 8, !tbaa !6
  %478 = load <4 x i64>, ptr %474, align 8, !tbaa !6
  %479 = load <4 x i64>, ptr %475, align 8, !tbaa !6
  %480 = add i32 %374, %470
  %481 = sext i32 %480 to i64
  %482 = getelementptr inbounds [96 x i64], ptr %4, i64 0, i64 %481
  %483 = getelementptr inbounds i8, ptr %482, i64 -24
  %484 = getelementptr inbounds i8, ptr %482, i64 -56
  %485 = getelementptr inbounds i8, ptr %482, i64 -88
  %486 = getelementptr inbounds i8, ptr %482, i64 -120
  store <4 x i64> %476, ptr %483, align 8, !tbaa !6
  store <4 x i64> %477, ptr %484, align 8, !tbaa !6
  store <4 x i64> %478, ptr %485, align 8, !tbaa !6
  store <4 x i64> %479, ptr %486, align 8, !tbaa !6
  %487 = add nuw i64 %467, 16
  %488 = icmp eq i64 %487, %465
  br i1 %488, label %489, label %466, !llvm.loop !77

489:                                              ; preds = %466
  %490 = icmp eq i64 %465, %449
  br i1 %490, label %595, label %491

491:                                              ; preds = %489
  %492 = sub nsw i64 %448, %465
  %493 = and i64 %449, 12
  %494 = icmp eq i64 %493, 0
  br i1 %494, label %515, label %495

495:                                              ; preds = %491, %462
  %496 = phi i64 [ %465, %491 ], [ 0, %462 ]
  %497 = and i64 %449, 4294967292
  %498 = sub nsw i64 %448, %497
  %499 = getelementptr i8, ptr %4, i64 -24
  %500 = getelementptr i8, ptr %4, i64 -24
  br label %501

501:                                              ; preds = %501, %495
  %502 = phi i64 [ %496, %495 ], [ %511, %501 ]
  %503 = sub i64 %448, %502
  %504 = trunc i64 %502 to i32
  %505 = sub i32 %445, %504
  %506 = getelementptr [96 x i64], ptr %499, i64 0, i64 %503
  %507 = load <4 x i64>, ptr %506, align 8, !tbaa !6
  %508 = add i32 %374, %505
  %509 = sext i32 %508 to i64
  %510 = getelementptr [96 x i64], ptr %500, i64 0, i64 %509
  store <4 x i64> %507, ptr %510, align 8, !tbaa !6
  %511 = add nuw i64 %502, 4
  %512 = icmp eq i64 %511, %497
  br i1 %512, label %513, label %501, !llvm.loop !78

513:                                              ; preds = %501
  %514 = icmp eq i64 %497, %449
  br i1 %514, label %595, label %515

515:                                              ; preds = %491, %513, %455, %451, %447
  %516 = phi i64 [ %448, %447 ], [ %448, %451 ], [ %448, %455 ], [ %492, %491 ], [ %498, %513 ]
  %517 = add nsw i64 %516, 1
  %518 = and i64 %517, 7
  %519 = and i64 %516, 7
  %520 = icmp eq i64 %519, 7
  br i1 %520, label %533, label %521

521:                                              ; preds = %515, %521
  %522 = phi i64 [ %530, %521 ], [ %516, %515 ]
  %523 = phi i64 [ %531, %521 ], [ 0, %515 ]
  %524 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %522
  %525 = load i64, ptr %524, align 8, !tbaa !6
  %526 = trunc i64 %522 to i32
  %527 = add i32 %374, %526
  %528 = sext i32 %527 to i64
  %529 = getelementptr inbounds [96 x i64], ptr %4, i64 0, i64 %528
  store i64 %525, ptr %529, align 8, !tbaa !6
  %530 = add nsw i64 %522, -1
  %531 = add i64 %523, 1
  %532 = icmp eq i64 %531, %518
  br i1 %532, label %533, label %521, !llvm.loop !79

533:                                              ; preds = %521, %515
  %534 = phi i64 [ %516, %515 ], [ %530, %521 ]
  %535 = icmp ult i64 %516, 7
  br i1 %535, label %595, label %536

536:                                              ; preds = %533, %536
  %537 = phi i64 [ %593, %536 ], [ %534, %533 ]
  %538 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %537
  %539 = load i64, ptr %538, align 8, !tbaa !6
  %540 = trunc i64 %537 to i32
  %541 = add i32 %374, %540
  %542 = sext i32 %541 to i64
  %543 = getelementptr inbounds [96 x i64], ptr %4, i64 0, i64 %542
  store i64 %539, ptr %543, align 8, !tbaa !6
  %544 = add nsw i64 %537, -1
  %545 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %544
  %546 = load i64, ptr %545, align 8, !tbaa !6
  %547 = trunc i64 %544 to i32
  %548 = add i32 %374, %547
  %549 = sext i32 %548 to i64
  %550 = getelementptr inbounds [96 x i64], ptr %4, i64 0, i64 %549
  store i64 %546, ptr %550, align 8, !tbaa !6
  %551 = add nsw i64 %537, -2
  %552 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %551
  %553 = load i64, ptr %552, align 8, !tbaa !6
  %554 = trunc i64 %551 to i32
  %555 = add i32 %374, %554
  %556 = sext i32 %555 to i64
  %557 = getelementptr inbounds [96 x i64], ptr %4, i64 0, i64 %556
  store i64 %553, ptr %557, align 8, !tbaa !6
  %558 = add nsw i64 %537, -3
  %559 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %558
  %560 = load i64, ptr %559, align 8, !tbaa !6
  %561 = trunc i64 %558 to i32
  %562 = add i32 %374, %561
  %563 = sext i32 %562 to i64
  %564 = getelementptr inbounds [96 x i64], ptr %4, i64 0, i64 %563
  store i64 %560, ptr %564, align 8, !tbaa !6
  %565 = add nsw i64 %537, -4
  %566 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %565
  %567 = load i64, ptr %566, align 8, !tbaa !6
  %568 = trunc i64 %565 to i32
  %569 = add i32 %374, %568
  %570 = sext i32 %569 to i64
  %571 = getelementptr inbounds [96 x i64], ptr %4, i64 0, i64 %570
  store i64 %567, ptr %571, align 8, !tbaa !6
  %572 = add nsw i64 %537, -5
  %573 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %572
  %574 = load i64, ptr %573, align 8, !tbaa !6
  %575 = trunc i64 %572 to i32
  %576 = add i32 %374, %575
  %577 = sext i32 %576 to i64
  %578 = getelementptr inbounds [96 x i64], ptr %4, i64 0, i64 %577
  store i64 %574, ptr %578, align 8, !tbaa !6
  %579 = add nsw i64 %537, -6
  %580 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %579
  %581 = load i64, ptr %580, align 8, !tbaa !6
  %582 = trunc i64 %579 to i32
  %583 = add i32 %374, %582
  %584 = sext i32 %583 to i64
  %585 = getelementptr inbounds [96 x i64], ptr %4, i64 0, i64 %584
  store i64 %581, ptr %585, align 8, !tbaa !6
  %586 = add nsw i64 %537, -7
  %587 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %586
  %588 = load i64, ptr %587, align 8, !tbaa !6
  %589 = trunc i64 %586 to i32
  %590 = add i32 %374, %589
  %591 = sext i32 %590 to i64
  %592 = getelementptr inbounds [96 x i64], ptr %4, i64 0, i64 %591
  store i64 %588, ptr %592, align 8, !tbaa !6
  %593 = add nsw i64 %537, -8
  %594 = icmp eq i64 %586, 0
  br i1 %594, label %595, label %536, !llvm.loop !80

595:                                              ; preds = %533, %536, %489, %513, %444
  %596 = lshr i32 %370, 3
  %597 = and i32 %596, 536870904
  %598 = zext nneg i32 %597 to i64
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 8 dereferenceable(1) %4, i8 0, i64 %598, i1 false), !tbaa !6
  %599 = add i32 %442, %374
  store i32 %599, ptr %360, align 8, !tbaa !48
  br label %600

600:                                              ; preds = %595, %441, %368, %366
  %601 = getelementptr inbounds nuw i8, ptr %0, i64 1544
  %602 = load i32, ptr %601, align 8, !tbaa !48
  %603 = getelementptr inbounds nuw i8, ptr %5, i64 768
  store i32 %602, ptr %603, align 8, !tbaa !48
  %604 = icmp eq i32 %602, 0
  br i1 %604, label %920, label %605

605:                                              ; preds = %600
  %606 = getelementptr inbounds nuw i8, ptr %0, i64 776
  %607 = sext i32 %602 to i64
  %608 = shl nsw i64 %607, 3
  %609 = call ptr @__memcpy_chk(ptr noundef nonnull %5, ptr noundef nonnull readonly %606, i64 noundef range(i64 -17179869184, 17179869177) %608, i64 noundef 776) #11, !alias.scope !81
  %610 = load i32, ptr %603, align 8, !tbaa !48
  %611 = icmp sgt i32 %610, 0
  br i1 %611, label %612, label %688

612:                                              ; preds = %605
  %613 = zext i64 %1 to i128
  %614 = zext nneg i32 %610 to i64
  %615 = and i64 %614, 3
  %616 = icmp ult i32 %610, 4
  br i1 %616, label %621, label %617

617:                                              ; preds = %612
  %618 = and i64 %614, 2147483644
  br label %650

619:                                              ; preds = %650
  %620 = trunc nuw i128 %684 to i64
  br label %621

621:                                              ; preds = %619, %612
  %622 = phi i128 [ poison, %612 ], [ %682, %619 ]
  %623 = phi i64 [ poison, %612 ], [ %620, %619 ]
  %624 = phi i64 [ 0, %612 ], [ %685, %619 ]
  %625 = phi i128 [ 0, %612 ], [ %684, %619 ]
  %626 = icmp eq i64 %615, 0
  br i1 %626, label %643, label %627

627:                                              ; preds = %621, %627
  %628 = phi i64 [ %638, %627 ], [ %624, %621 ]
  %629 = phi i128 [ %637, %627 ], [ %625, %621 ]
  %630 = phi i64 [ %639, %627 ], [ 0, %621 ]
  %631 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %628
  %632 = load i64, ptr %631, align 8, !tbaa !6
  %633 = zext i64 %632 to i128
  %634 = mul nuw i128 %633, %613
  %635 = add nuw i128 %634, %629
  %636 = trunc i128 %635 to i64
  store i64 %636, ptr %631, align 8, !tbaa !6
  %637 = lshr i128 %635, 64
  %638 = add nuw nsw i64 %628, 1
  %639 = add i64 %630, 1
  %640 = icmp eq i64 %639, %615
  br i1 %640, label %641, label %627, !llvm.loop !85

641:                                              ; preds = %627
  %642 = trunc nuw i128 %637 to i64
  br label %643

643:                                              ; preds = %621, %641
  %644 = phi i128 [ %622, %621 ], [ %635, %641 ]
  %645 = phi i64 [ %623, %621 ], [ %642, %641 ]
  %646 = icmp ult i128 %644, 18446744073709551616
  br i1 %646, label %688, label %647

647:                                              ; preds = %643
  %648 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %614
  store i64 %645, ptr %648, align 8, !tbaa !6
  %649 = add nuw i32 %610, 1
  br label %688

650:                                              ; preds = %650, %617
  %651 = phi i64 [ 0, %617 ], [ %685, %650 ]
  %652 = phi i128 [ 0, %617 ], [ %684, %650 ]
  %653 = phi i64 [ 0, %617 ], [ %686, %650 ]
  %654 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %651
  %655 = load i64, ptr %654, align 8, !tbaa !6
  %656 = zext i64 %655 to i128
  %657 = mul nuw i128 %656, %613
  %658 = add nuw i128 %657, %652
  %659 = trunc i128 %658 to i64
  store i64 %659, ptr %654, align 8, !tbaa !6
  %660 = lshr i128 %658, 64
  %661 = or disjoint i64 %651, 1
  %662 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %661
  %663 = load i64, ptr %662, align 8, !tbaa !6
  %664 = zext i64 %663 to i128
  %665 = mul nuw i128 %664, %613
  %666 = add nuw i128 %665, %660
  %667 = trunc i128 %666 to i64
  store i64 %667, ptr %662, align 8, !tbaa !6
  %668 = lshr i128 %666, 64
  %669 = or disjoint i64 %651, 2
  %670 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %669
  %671 = load i64, ptr %670, align 8, !tbaa !6
  %672 = zext i64 %671 to i128
  %673 = mul nuw i128 %672, %613
  %674 = add nuw i128 %673, %668
  %675 = trunc i128 %674 to i64
  store i64 %675, ptr %670, align 8, !tbaa !6
  %676 = lshr i128 %674, 64
  %677 = or disjoint i64 %651, 3
  %678 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %677
  %679 = load i64, ptr %678, align 8, !tbaa !6
  %680 = zext i64 %679 to i128
  %681 = mul nuw i128 %680, %613
  %682 = add nuw i128 %681, %676
  %683 = trunc i128 %682 to i64
  store i64 %683, ptr %678, align 8, !tbaa !6
  %684 = lshr i128 %682, 64
  %685 = add nuw nsw i64 %651, 4
  %686 = add i64 %653, 4
  %687 = icmp eq i64 %686, %618
  br i1 %687, label %619, label %650, !llvm.loop !45

688:                                              ; preds = %605, %643, %647
  %689 = phi i32 [ %610, %605 ], [ %610, %643 ], [ %649, %647 ]
  %690 = icmp sgt i64 %2, 0
  br i1 %690, label %691, label %920

691:                                              ; preds = %688
  %692 = icmp eq i32 %689, 0
  br i1 %692, label %920, label %693

693:                                              ; preds = %691
  %694 = trunc nuw nsw i64 %2 to i32
  %695 = lshr i32 %694, 6
  %696 = and i32 %694, 63
  %697 = icmp ne i32 %696, 0
  %698 = icmp sgt i32 %689, 0
  %699 = and i1 %697, %698
  br i1 %699, label %700, label %762

700:                                              ; preds = %693
  %701 = and i64 %2, 63
  %702 = sub nuw nsw i32 64, %696
  %703 = zext nneg i32 %702 to i64
  %704 = zext nneg i32 %689 to i64
  %705 = and i64 %704, 3
  %706 = icmp ult i32 %689, 4
  br i1 %706, label %709, label %707

707:                                              ; preds = %700
  %708 = and i64 %704, 2147483644
  br label %729

709:                                              ; preds = %729, %700
  %710 = phi i64 [ poison, %700 ], [ %755, %729 ]
  %711 = phi i64 [ 0, %700 ], [ %756, %729 ]
  %712 = phi i64 [ 0, %700 ], [ %755, %729 ]
  %713 = icmp eq i64 %705, 0
  br i1 %713, label %726, label %714

714:                                              ; preds = %709, %714
  %715 = phi i64 [ %723, %714 ], [ %711, %709 ]
  %716 = phi i64 [ %722, %714 ], [ %712, %709 ]
  %717 = phi i64 [ %724, %714 ], [ 0, %709 ]
  %718 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %715
  %719 = load i64, ptr %718, align 8, !tbaa !6
  %720 = shl i64 %719, %701
  %721 = or i64 %720, %716
  store i64 %721, ptr %718, align 8, !tbaa !6
  %722 = lshr i64 %719, %703
  %723 = add nuw nsw i64 %715, 1
  %724 = add i64 %717, 1
  %725 = icmp eq i64 %724, %705
  br i1 %725, label %726, label %714, !llvm.loop !86

726:                                              ; preds = %714, %709
  %727 = phi i64 [ %710, %709 ], [ %722, %714 ]
  %728 = icmp eq i64 %727, 0
  br i1 %728, label %762, label %759

729:                                              ; preds = %729, %707
  %730 = phi i64 [ 0, %707 ], [ %756, %729 ]
  %731 = phi i64 [ 0, %707 ], [ %755, %729 ]
  %732 = phi i64 [ 0, %707 ], [ %757, %729 ]
  %733 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %730
  %734 = load i64, ptr %733, align 8, !tbaa !6
  %735 = shl i64 %734, %701
  %736 = or i64 %735, %731
  store i64 %736, ptr %733, align 8, !tbaa !6
  %737 = lshr i64 %734, %703
  %738 = or disjoint i64 %730, 1
  %739 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %738
  %740 = load i64, ptr %739, align 8, !tbaa !6
  %741 = shl i64 %740, %701
  %742 = or i64 %741, %737
  store i64 %742, ptr %739, align 8, !tbaa !6
  %743 = lshr i64 %740, %703
  %744 = or disjoint i64 %730, 2
  %745 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %744
  %746 = load i64, ptr %745, align 8, !tbaa !6
  %747 = shl i64 %746, %701
  %748 = or i64 %747, %743
  store i64 %748, ptr %745, align 8, !tbaa !6
  %749 = lshr i64 %746, %703
  %750 = or disjoint i64 %730, 3
  %751 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %750
  %752 = load i64, ptr %751, align 8, !tbaa !6
  %753 = shl i64 %752, %701
  %754 = or i64 %753, %749
  store i64 %754, ptr %751, align 8, !tbaa !6
  %755 = lshr i64 %752, %703
  %756 = add nuw nsw i64 %730, 4
  %757 = add i64 %732, 4
  %758 = icmp eq i64 %757, %708
  br i1 %758, label %709, label %729, !llvm.loop !64

759:                                              ; preds = %726
  %760 = add nuw i32 %689, 1
  %761 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %704
  store i64 %727, ptr %761, align 8, !tbaa !6
  br label %762

762:                                              ; preds = %759, %726, %693
  %763 = phi i32 [ %689, %726 ], [ %760, %759 ], [ %689, %693 ]
  %764 = icmp samesign ult i64 %2, 64
  br i1 %764, label %920, label %765

765:                                              ; preds = %762
  %766 = add i32 %763, -1
  %767 = icmp sgt i32 %766, -1
  br i1 %767, label %768, label %916

768:                                              ; preds = %765
  %769 = zext nneg i32 %766 to i64
  %770 = zext i32 %763 to i64
  %771 = icmp ult i32 %763, 4
  br i1 %771, label %836, label %772

772:                                              ; preds = %768
  %773 = add i32 %763, %695
  %774 = add i32 %773, -1
  %775 = icmp sgt i32 %695, %774
  br i1 %775, label %836, label %776

776:                                              ; preds = %772
  %777 = add i32 %763, %695
  %778 = add i32 %777, -1
  %779 = sext i32 %778 to i64
  %780 = sub nsw i64 %769, %779
  %781 = and i64 %780, 2305843009213693936
  %782 = icmp eq i64 %781, 0
  br i1 %782, label %836, label %783

783:                                              ; preds = %776
  %784 = icmp ult i32 %763, 16
  br i1 %784, label %816, label %785

785:                                              ; preds = %783
  %786 = and i64 %770, 4294967280
  br label %787

787:                                              ; preds = %787, %785
  %788 = phi i64 [ 0, %785 ], [ %808, %787 ]
  %789 = sub i64 %769, %788
  %790 = trunc i64 %788 to i32
  %791 = sub i32 %766, %790
  %792 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %789
  %793 = getelementptr inbounds i8, ptr %792, i64 -24
  %794 = getelementptr inbounds i8, ptr %792, i64 -56
  %795 = getelementptr inbounds i8, ptr %792, i64 -88
  %796 = getelementptr inbounds i8, ptr %792, i64 -120
  %797 = load <4 x i64>, ptr %793, align 8, !tbaa !6
  %798 = load <4 x i64>, ptr %794, align 8, !tbaa !6
  %799 = load <4 x i64>, ptr %795, align 8, !tbaa !6
  %800 = load <4 x i64>, ptr %796, align 8, !tbaa !6
  %801 = add i32 %695, %791
  %802 = sext i32 %801 to i64
  %803 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %802
  %804 = getelementptr inbounds i8, ptr %803, i64 -24
  %805 = getelementptr inbounds i8, ptr %803, i64 -56
  %806 = getelementptr inbounds i8, ptr %803, i64 -88
  %807 = getelementptr inbounds i8, ptr %803, i64 -120
  store <4 x i64> %797, ptr %804, align 8, !tbaa !6
  store <4 x i64> %798, ptr %805, align 8, !tbaa !6
  store <4 x i64> %799, ptr %806, align 8, !tbaa !6
  store <4 x i64> %800, ptr %807, align 8, !tbaa !6
  %808 = add nuw i64 %788, 16
  %809 = icmp eq i64 %808, %786
  br i1 %809, label %810, label %787, !llvm.loop !87

810:                                              ; preds = %787
  %811 = icmp eq i64 %786, %770
  br i1 %811, label %916, label %812

812:                                              ; preds = %810
  %813 = sub nsw i64 %769, %786
  %814 = and i64 %770, 12
  %815 = icmp eq i64 %814, 0
  br i1 %815, label %836, label %816

816:                                              ; preds = %812, %783
  %817 = phi i64 [ %786, %812 ], [ 0, %783 ]
  %818 = and i64 %770, 4294967292
  %819 = sub nsw i64 %769, %818
  %820 = getelementptr i8, ptr %5, i64 -24
  %821 = getelementptr i8, ptr %5, i64 -24
  br label %822

822:                                              ; preds = %822, %816
  %823 = phi i64 [ %817, %816 ], [ %832, %822 ]
  %824 = sub i64 %769, %823
  %825 = trunc i64 %823 to i32
  %826 = sub i32 %766, %825
  %827 = getelementptr [96 x i64], ptr %820, i64 0, i64 %824
  %828 = load <4 x i64>, ptr %827, align 8, !tbaa !6
  %829 = add i32 %695, %826
  %830 = sext i32 %829 to i64
  %831 = getelementptr [96 x i64], ptr %821, i64 0, i64 %830
  store <4 x i64> %828, ptr %831, align 8, !tbaa !6
  %832 = add nuw i64 %823, 4
  %833 = icmp eq i64 %832, %818
  br i1 %833, label %834, label %822, !llvm.loop !88

834:                                              ; preds = %822
  %835 = icmp eq i64 %818, %770
  br i1 %835, label %916, label %836

836:                                              ; preds = %812, %834, %776, %772, %768
  %837 = phi i64 [ %769, %768 ], [ %769, %772 ], [ %769, %776 ], [ %813, %812 ], [ %819, %834 ]
  %838 = add nsw i64 %837, 1
  %839 = and i64 %838, 7
  %840 = and i64 %837, 7
  %841 = icmp eq i64 %840, 7
  br i1 %841, label %854, label %842

842:                                              ; preds = %836, %842
  %843 = phi i64 [ %851, %842 ], [ %837, %836 ]
  %844 = phi i64 [ %852, %842 ], [ 0, %836 ]
  %845 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %843
  %846 = load i64, ptr %845, align 8, !tbaa !6
  %847 = trunc i64 %843 to i32
  %848 = add i32 %695, %847
  %849 = sext i32 %848 to i64
  %850 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %849
  store i64 %846, ptr %850, align 8, !tbaa !6
  %851 = add nsw i64 %843, -1
  %852 = add i64 %844, 1
  %853 = icmp eq i64 %852, %839
  br i1 %853, label %854, label %842, !llvm.loop !89

854:                                              ; preds = %842, %836
  %855 = phi i64 [ %837, %836 ], [ %851, %842 ]
  %856 = icmp ult i64 %837, 7
  br i1 %856, label %916, label %857

857:                                              ; preds = %854, %857
  %858 = phi i64 [ %914, %857 ], [ %855, %854 ]
  %859 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %858
  %860 = load i64, ptr %859, align 8, !tbaa !6
  %861 = trunc i64 %858 to i32
  %862 = add i32 %695, %861
  %863 = sext i32 %862 to i64
  %864 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %863
  store i64 %860, ptr %864, align 8, !tbaa !6
  %865 = add nsw i64 %858, -1
  %866 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %865
  %867 = load i64, ptr %866, align 8, !tbaa !6
  %868 = trunc i64 %865 to i32
  %869 = add i32 %695, %868
  %870 = sext i32 %869 to i64
  %871 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %870
  store i64 %867, ptr %871, align 8, !tbaa !6
  %872 = add nsw i64 %858, -2
  %873 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %872
  %874 = load i64, ptr %873, align 8, !tbaa !6
  %875 = trunc i64 %872 to i32
  %876 = add i32 %695, %875
  %877 = sext i32 %876 to i64
  %878 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %877
  store i64 %874, ptr %878, align 8, !tbaa !6
  %879 = add nsw i64 %858, -3
  %880 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %879
  %881 = load i64, ptr %880, align 8, !tbaa !6
  %882 = trunc i64 %879 to i32
  %883 = add i32 %695, %882
  %884 = sext i32 %883 to i64
  %885 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %884
  store i64 %881, ptr %885, align 8, !tbaa !6
  %886 = add nsw i64 %858, -4
  %887 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %886
  %888 = load i64, ptr %887, align 8, !tbaa !6
  %889 = trunc i64 %886 to i32
  %890 = add i32 %695, %889
  %891 = sext i32 %890 to i64
  %892 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %891
  store i64 %888, ptr %892, align 8, !tbaa !6
  %893 = add nsw i64 %858, -5
  %894 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %893
  %895 = load i64, ptr %894, align 8, !tbaa !6
  %896 = trunc i64 %893 to i32
  %897 = add i32 %695, %896
  %898 = sext i32 %897 to i64
  %899 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %898
  store i64 %895, ptr %899, align 8, !tbaa !6
  %900 = add nsw i64 %858, -6
  %901 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %900
  %902 = load i64, ptr %901, align 8, !tbaa !6
  %903 = trunc i64 %900 to i32
  %904 = add i32 %695, %903
  %905 = sext i32 %904 to i64
  %906 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %905
  store i64 %902, ptr %906, align 8, !tbaa !6
  %907 = add nsw i64 %858, -7
  %908 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %907
  %909 = load i64, ptr %908, align 8, !tbaa !6
  %910 = trunc i64 %907 to i32
  %911 = add i32 %695, %910
  %912 = sext i32 %911 to i64
  %913 = getelementptr inbounds [96 x i64], ptr %5, i64 0, i64 %912
  store i64 %909, ptr %913, align 8, !tbaa !6
  %914 = add nsw i64 %858, -8
  %915 = icmp eq i64 %907, 0
  br i1 %915, label %916, label %857, !llvm.loop !90

916:                                              ; preds = %854, %857, %810, %834, %765
  %917 = lshr i64 %2, 3
  %918 = and i64 %917, 536870904
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 8 dereferenceable(1) %5, i8 0, i64 %918, i1 false), !tbaa !6
  %919 = add i32 %763, %695
  br label %920

920:                                              ; preds = %600, %916, %762, %691, %688
  %921 = phi i32 [ %919, %916 ], [ %763, %762 ], [ 0, %691 ], [ %689, %688 ], [ 0, %600 ]
  %922 = load i32, ptr %360, align 8, !tbaa !48
  %923 = icmp eq i32 %922, %921
  br i1 %923, label %924, label %926

924:                                              ; preds = %920
  %925 = zext i32 %921 to i64
  br label %929

926:                                              ; preds = %920
  %927 = icmp slt i32 %922, %921
  %928 = select i1 %927, i32 -1, i32 1
  br label %944

929:                                              ; preds = %934, %924
  %930 = phi i64 [ %925, %924 ], [ %931, %934 ]
  %931 = add nsw i64 %930, -1
  %932 = and i64 %931, 2147483648
  %933 = icmp eq i64 %932, 0
  br i1 %933, label %934, label %944

934:                                              ; preds = %929
  %935 = and i64 %931, 2147483647
  %936 = getelementptr inbounds nuw [96 x i64], ptr %4, i64 0, i64 %935
  %937 = load i64, ptr %936, align 8, !tbaa !6
  %938 = getelementptr inbounds nuw [96 x i64], ptr %5, i64 0, i64 %935
  %939 = load i64, ptr %938, align 8, !tbaa !6
  %940 = icmp eq i64 %937, %939
  br i1 %940, label %929, label %941, !llvm.loop !71

941:                                              ; preds = %934
  %942 = icmp ult i64 %937, %939
  %943 = select i1 %942, i32 -1, i32 1
  br label %944

944:                                              ; preds = %342, %929, %354, %339, %941, %926
  %945 = phi i32 [ %928, %926 ], [ %943, %941 ], [ %341, %339 ], [ %356, %354 ], [ 0, %929 ], [ 1, %342 ]
  call void @llvm.lifetime.end.p0(i64 776, ptr nonnull %5) #11
  call void @llvm.lifetime.end.p0(i64 776, ptr nonnull %4) #11
  ret i32 %945
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.umin.i64(i64, i64) #9

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr writeonly captures(none), i8, i64, i1 immarg) #10

attributes #0 = { nounwind sspstrong uwtable "frame-pointer"="all" "min-legal-vector-width"="128" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64-v3" "target-features"="+avx,+avx2,+bmi,+bmi2,+cmov,+crc32,+cx16,+cx8,+f16c,+fma,+fxsr,+lzcnt,+mmx,+movbe,+pclmul,+popcnt,+sahf,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3,+x87,+xsave" "zero-call-used-regs"="used-gpr" }
attributes #1 = { mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #2 = { cold noreturn nounwind memory(inaccessiblemem: write) }
attributes #3 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="x86-64-v3" "target-features"="+avx,+avx2,+bmi,+bmi2,+cmov,+crc32,+cx16,+cx8,+f16c,+fma,+fxsr,+lzcnt,+mmx,+movbe,+pclmul,+popcnt,+sahf,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3,+x87,+xsave" "zero-call-used-regs"="used-gpr" }
attributes #4 = { nocallback nofree nounwind memory(argmem: readwrite) "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="x86-64-v3" "target-features"="+avx,+avx2,+bmi,+bmi2,+cmov,+crc32,+cx16,+cx8,+f16c,+fma,+fxsr,+lzcnt,+mmx,+movbe,+pclmul,+popcnt,+sahf,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3,+x87,+xsave" "zero-call-used-regs"="used-gpr" }
attributes #5 = { nofree norecurse nounwind sspstrong memory(argmem: readwrite) uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64-v3" "target-features"="+avx,+avx2,+bmi,+bmi2,+cmov,+crc32,+cx16,+cx8,+f16c,+fma,+fxsr,+lzcnt,+mmx,+movbe,+pclmul,+popcnt,+sahf,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3,+x87,+xsave" "zero-call-used-regs"="used-gpr" }
attributes #6 = { mustprogress nocallback nofree nosync nounwind willreturn memory(none) }
attributes #7 = { mustprogress nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #8 = { nofree norecurse nosync nounwind sspstrong memory(argmem: readwrite) uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "probe-stack"="inline-asm" "stack-protector-buffer-size"="4" "target-cpu"="x86-64-v3" "target-features"="+avx,+avx2,+bmi,+bmi2,+cmov,+crc32,+cx16,+cx8,+f16c,+fma,+fxsr,+lzcnt,+mmx,+movbe,+pclmul,+popcnt,+sahf,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3,+x87,+xsave" "zero-call-used-regs"="used-gpr" }
attributes #9 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #10 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #11 = { nounwind }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 4, !"probe-stack", !"inline-asm"}
!2 = !{i32 8, !"PIC Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"clang version 21.1.8"}
!6 = !{!7, !7, i64 0}
!7 = !{!"long", !8, i64 0}
!8 = !{!"omnipotent char", !9, i64 0}
!9 = !{!"Simple C/C++ TBAA"}
!10 = !{!11, !11, i64 0}
!11 = !{!"int", !8, i64 0}
!12 = !{!8, !8, i64 0}
!13 = distinct !{!13, !14}
!14 = !{!"llvm.loop.mustprogress"}
!15 = distinct !{!15, !14}
!16 = distinct !{!16, !14}
!17 = distinct !{!17, !14}
!18 = distinct !{!18, !14}
!19 = !{!20, !20, i64 0}
!20 = !{!"double", !8, i64 0}
!21 = !{!22, !7, i64 0}
!22 = !{!"", !7, i64 0, !7, i64 8, !11, i64 16}
!23 = !{!"branch_weights", !"expected", i32 1, i32 2000}
!24 = !{!22, !7, i64 8}
!25 = !{!22, !11, i64 16}
!26 = distinct !{!26, !14}
!27 = distinct !{!27, !14}
!28 = distinct !{!28, !14}
!29 = distinct !{!29, !14}
!30 = distinct !{!30, !14}
!31 = distinct !{!31, !14}
!32 = distinct !{!32, !14}
!33 = distinct !{!33, !14}
!34 = distinct !{!34, !14}
!35 = distinct !{!35, !14, !36}
!36 = !{!"llvm.loop.peeled.count", i32 1}
!37 = distinct !{!37, !14}
!38 = distinct !{!38, !39}
!39 = !{!"llvm.loop.unroll.disable"}
!40 = !{!41, !11, i64 1560}
!41 = !{!"", !42, i64 0, !42, i64 776, !7, i64 1552, !11, i64 1560}
!42 = !{!"", !8, i64 0, !11, i64 768}
!43 = !{!41, !7, i64 1552}
!44 = distinct !{!44, !39}
!45 = distinct !{!45, !14}
!46 = distinct !{!46, !14}
!47 = distinct !{!47, !39}
!48 = !{!42, !11, i64 768}
!49 = distinct !{!49, !39}
!50 = distinct !{!50, !14}
!51 = distinct !{!51, !39}
!52 = distinct !{!52, !39}
!53 = distinct !{!53, !14}
!54 = distinct !{!54, !39}
!55 = distinct !{!55, !14}
!56 = distinct !{!56, !39}
!57 = distinct !{!57, !39}
!58 = !{!59, !61}
!59 = distinct !{!59, !60, !"memcpy.inline: argument 0"}
!60 = distinct !{!60, !"memcpy.inline"}
!61 = distinct !{!61, !60, !"memcpy.inline: argument 1"}
!62 = distinct !{!62, !39}
!63 = distinct !{!63, !39}
!64 = distinct !{!64, !14}
!65 = distinct !{!65, !14, !66, !67}
!66 = !{!"llvm.loop.isvectorized", i32 1}
!67 = !{!"llvm.loop.unroll.runtime.disable"}
!68 = distinct !{!68, !14, !66, !67}
!69 = distinct !{!69, !39}
!70 = distinct !{!70, !14, !66}
!71 = distinct !{!71, !14}
!72 = !{!73, !75}
!73 = distinct !{!73, !74, !"memcpy.inline: argument 0"}
!74 = distinct !{!74, !"memcpy.inline"}
!75 = distinct !{!75, !74, !"memcpy.inline: argument 1"}
!76 = distinct !{!76, !39}
!77 = distinct !{!77, !14, !66, !67}
!78 = distinct !{!78, !14, !66, !67}
!79 = distinct !{!79, !39}
!80 = distinct !{!80, !14, !66}
!81 = !{!82, !84}
!82 = distinct !{!82, !83, !"memcpy.inline: argument 0"}
!83 = distinct !{!83, !"memcpy.inline"}
!84 = distinct !{!84, !83, !"memcpy.inline: argument 1"}
!85 = distinct !{!85, !39}
!86 = distinct !{!86, !39}
!87 = distinct !{!87, !14, !66, !67}
!88 = distinct !{!88, !14, !66, !67}
!89 = distinct !{!89, !39}
!90 = distinct !{!90, !14, !66}
