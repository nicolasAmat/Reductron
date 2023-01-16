<?xml version="1.0"?>

<xsl:stylesheet version="1.0"
  xmlns:pnml="http://www.pnml.org/version-2009/grammar/pnml"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

  <xsl:output method="text" encoding="UTF-8" media-type="text/plain" />

  <!-- Begin of templates. -->
  <xsl:template match="/">
    <xsl:apply-templates select="pnml/net/page|pnml:pnml/pnml:net/pnml:page" />
  </xsl:template>

  <xsl:template match="page|pnml:page">
    <xsl:text>/* This file was automatically generated from PNML */
  
model </xsl:text>
    <xsl:value-of select="../name/text|../pnml:name/pnml:text" />
    <xsl:text> {

var </xsl:text>
    <xsl:apply-templates
      select="place|pnml:place" mode="vars">
      <xsl:with-param name="tot" select="count(place|pnml:place)" />
    </xsl:apply-templates>
    <xsl:text>;</xsl:text>
    <xsl:text>

states marking;

    </xsl:text>
    <xsl:apply-templates
      select="transition|pnml:transition" />
    <xsl:text>
}</xsl:text>
<xsl:text>

strategy strat {
 setMaxState(2000);
 setMaxAcc(100);

 Region init := {</xsl:text>
      <xsl:apply-templates select="place/initialMarking|pnml:place/pnml:initialMarking" />
      <xsl:text>state=marking};

 Transitions trans := {</xsl:text>
  <xsl:apply-templates select="transition/name|pnml:transition/pnml:name">
      <xsl:with-param name="last" select="/pnml/net/page/transition[last()]/@id|/pnml:pnml/pnml:net/pnml:page/pnml:transition[last()]/@id" />
    </xsl:apply-templates>
  <xsl:text>}; 

 Region reach := post*(init, trans, 1); 
} 
    </xsl:text>
  </xsl:template>

  <xsl:template match="transition/name|pnml:transition/pnml:name">
    <xsl:param name="last" />
    <xsl:value-of select="./text|./pnml:text" />
    <xsl:choose>
      <xsl:when test="$last!=../@id">
        <xsl:text>, </xsl:text>
      </xsl:when>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="transition|pnml:transition">
    <xsl:variable name="nametrans" select="./name/text|./pnml:name/pnml:text" />
    <xsl:variable
      name="ident" select="@id" />
    <xsl:variable name="lastg">
      <xsl:value-of
        select="../arc[@target=$ident][last()]/@id| ../pnml:arc[@target=$ident][last()]/@id" />
    </xsl:variable>
    <xsl:text>
transition </xsl:text>
    <xsl:value-of
      select="$nametrans" />
    <xsl:text> := {
 from := marking;
 to := marking;
 guard := </xsl:text><xsl:apply-templates
      select="../arc|../pnml:arc"
      mode="guard">
      <xsl:with-param name="transit" select="$ident" />
      <xsl:with-param
        name="lastg" select="$lastg" />
    </xsl:apply-templates>
  <xsl:text>
 action </xsl:text>
      <xsl:variable
      name="firstplace">
      <xsl:call-template name="firstplace">
        <xsl:with-param
          name="placenum" select="1" />
        <xsl:with-param
          name="trans" select="$ident" />
      </xsl:call-template>
    </xsl:variable>

      <xsl:apply-templates select="../place|../pnml:place" mode="connected">
      <xsl:with-param name="firstplace" select="$firstplace" />
        <xsl:with-param name="trans" select="$ident" /> 
      </xsl:apply-templates> 
      <xsl:text>;</xsl:text>
      <xsl:text>
};
    </xsl:text>
  </xsl:template>

  <xsl:template name="arcvalue">
    <xsl:variable name="arcval"
      select="./inscription/text|./inscription/value|./pnml:inscription/pnml:text|./pnml:inscription/pnml:value" />
    <xsl:choose>
      <xsl:when test="string-length($arcval)!=0">
        <xsl:value-of select="$arcval" />
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>1</xsl:text>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="arc|pnml:arc" mode="guard">
    <xsl:param name="transit" />
    <xsl:param name="lastg" />
    <xsl:if test="@target=$transit">
      <xsl:variable name="source" select="@source" />
      <xsl:for-each select="../place|../pnml:place">
        <xsl:if test="@id=$source">
          <xsl:value-of select="./name/text|./pnml:name/pnml:text" />
        </xsl:if>
      </xsl:for-each>
      <xsl:text>>=</xsl:text>
      <xsl:call-template
        name="arcvalue" />
      <xsl:choose>
        <xsl:when test="@id!=$lastg">
          <xsl:text> &amp;&amp; </xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>;</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:if>
  </xsl:template>


  <xsl:template match="place|pnml:place" mode="vars">
    <xsl:param name="tot" select="0" />
    <xsl:value-of
      select="./name/value|./pnml:inscription/pnml:value|./name/text|./pnml:name/pnml:text" />

    <xsl:choose>
      <xsl:when test="position()!=$tot">
        <xsl:text>, </xsl:text>
      </xsl:when>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="firstplace">
    <xsl:param name="placenum" />
    <xsl:param name="trans" />
    <xsl:variable name="place"
      select="../place[$placenum]/@id|../pnml:place[$placenum]/@id" />
    <xsl:variable name="placeplus">
      <xsl:apply-templates
        select="../arc[@target=$place and @source=$trans]|../pnml:arc[@target=$place and @source=$trans]"
        mode="plus">
        <xsl:with-param name="diff" select="0" />
      </xsl:apply-templates>
    </xsl:variable>
    <xsl:variable
      name="placemoins" default="0">
      <xsl:apply-templates
        select="../arc[@target=$trans and @source=$place]|../pnml:arc[@target=$trans and @source=$place]"
        mode="plus">
        <xsl:with-param name="diff" select="0" />
      </xsl:apply-templates>
    </xsl:variable>
    <xsl:variable
      name="placediff">
      <xsl:choose>
        <xsl:when test="$placeplus='' and $placemoins=''">
          <xsl:value-of select="0" />
        </xsl:when>
        <xsl:when test="$placeplus=''">
          <xsl:value-of select="- $placemoins" />
        </xsl:when>
        <xsl:when test="$placemoins=''">
          <xsl:value-of select="$placeplus" />
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$placeplus - $placemoins" />
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:choose>
      <xsl:when test="$placediff!=0">
        <xsl:value-of select="$placenum" />
      </xsl:when>
      <xsl:otherwise>
        <xsl:variable name="newnum" select="$placenum + 1" />
        <xsl:call-template name="firstplace">
          <xsl:with-param name="placenum" select="$newnum" />
          <xsl:with-param name="trans" select="$trans" />
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="place|pnml:place" mode="connected">
    <xsl:param name="firstplace" />
    <xsl:param name="trans" />
    <xsl:variable name="place" select="@id" />
    <xsl:variable
      name="placename" select="./name/text|./pnml:name/pnml:text" />
    <xsl:variable
      name="placeplus">
      <xsl:apply-templates
        select="../arc[@target=$place and @source=$trans]|../pnml:arc[@target=$place and @source=$trans]"
        mode="plus">
        <xsl:with-param name="diff" select="0" />
      </xsl:apply-templates>
    </xsl:variable>
    <xsl:variable
      name="placemoins" default="0">
      <xsl:apply-templates
        select="../arc[@target=$trans and @source=$place]|../pnml:arc[@target=$trans and @source=$place]"
        mode="plus">
        <xsl:with-param name="diff" select="0" />
      </xsl:apply-templates>
    </xsl:variable>
    <xsl:variable
      name="placediff">
      <xsl:choose>
        <xsl:when test="$placeplus='' and $placemoins=''">
          <xsl:value-of select="0" />
        </xsl:when>
        <xsl:when test="$placeplus=''">
          <xsl:value-of select="- $placemoins" />
        </xsl:when>
        <xsl:when test="$placemoins=''">
          <xsl:value-of select="$placeplus" />
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$placeplus - $placemoins" />
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:if
      test="$placediff!=0">
      <xsl:choose>
        <xsl:when test="$firstplace=position()">
          <xsl:text>:= </xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>, </xsl:text>
        </xsl:otherwise>
      </xsl:choose>
      <xsl:value-of
        select="$placename" />
      <xsl:text>'=</xsl:text>
      <xsl:value-of select="$placename" />
      <xsl:if
        test="$placediff>0">
        <xsl:text>+</xsl:text>
      </xsl:if>
      <xsl:value-of select="$placediff" />
    </xsl:if>
  </xsl:template>

  <xsl:template match="arc|pnml:arc" mode="plus">
    <xsl:param name="diff" />
    <xsl:variable name="arcval">
      <xsl:call-template name="arcvalue" />
    </xsl:variable>
    <xsl:value-of select="$diff + $arcval" />
  </xsl:template>

  <xsl:template match="place/initialMarking|pnml:place/pnml:initialMarking">
    <xsl:value-of select="../name/text|../pnml:name/pnml:text" />
    <xsl:text>=</xsl:text>
    <xsl:variable
      name="initval" select="./text|pnml:text" />
    <xsl:choose>
      <xsl:when test="string-length($initval)!=0">
        <xsl:value-of select="$initval" />
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>0</xsl:text>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:text> &amp;&amp; </xsl:text>
  </xsl:template>

</xsl:stylesheet>