// jTDS JDBC Driver for Microsoft SQL Server and Sybase
// Copyright (C) 2004 The jTDS Project
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License along with this library; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
//
package net.sourceforge.jtds.jdbcx.proxy;

import java.io.InputStream;
import java.io.Reader;
import java.math.BigDecimal;
import java.sql.*;
import java.util.Calendar;
import java.util.Map;

import net.sourceforge.jtds.jdbc.*;

/**
 * This class would be better implemented as a java.lang.reflect.Proxy.  However, this
 * feature was not added until 1.3 and reflection performance was not improved until 1.4.
 * Since the driver still needs to be compatible with 1.2 and 1.3 this class is used
 * to delegate the calls to a callable statement with minimal overhead.
 *
 * @version $Id: CallableStatementProxy.java,v 1.3 2004/08/24 17:45:08 bheineman Exp $
 */
public class CallableStatementProxy
extends PreparedStatementProxy
implements CallableStatement {
    private JtdsCallableStatement _callableStatement;
    
    CallableStatementProxy(ConnectionProxy connection, JtdsCallableStatement callableStatement) {
        super(connection, callableStatement);
        
        _callableStatement = callableStatement;
    }
    
    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void registerOutParameter(int parameterIndex, int sqlType) throws SQLException {
        validateConnection();

        try {
            _callableStatement.registerOutParameter(parameterIndex, sqlType);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void registerOutParameter(int parameterIndex, int sqlType, int scale) throws SQLException {
        validateConnection();

        try {
            _callableStatement.registerOutParameter(parameterIndex, sqlType, scale);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public boolean wasNull() throws SQLException {
        validateConnection();

        try {
            return _callableStatement.wasNull();
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return false;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public String getString(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getString(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public boolean getBoolean(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getBoolean(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return false;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public byte getByte(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getByte(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return Byte.MIN_VALUE;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public short getShort(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getShort(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return Short.MIN_VALUE;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public int getInt(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getInt(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return Integer.MIN_VALUE;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public long getLong(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getLong(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return Long.MIN_VALUE;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public float getFloat(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getFloat(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return Float.MIN_VALUE;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public double getDouble(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getDouble(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return Double.MIN_VALUE;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public BigDecimal getBigDecimal(int parameterIndex, int scale) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getBigDecimal(parameterIndex, scale);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public byte[] getBytes(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getBytes(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Date getDate(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getDate(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Time getTime(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getTime(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Timestamp getTimestamp(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getTimestamp(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Object getObject(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getObject(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public BigDecimal getBigDecimal(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getBigDecimal(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Object getObject(int parameterIndex, java.util.Map map) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getObject(parameterIndex, map);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Ref getRef(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getRef(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Blob getBlob(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getBlob(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Clob getClob(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getClob(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Array getArray(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getArray(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Date getDate(int parameterIndex, Calendar cal) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getDate(parameterIndex, cal);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Time getTime(int parameterIndex, Calendar cal) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getTime(parameterIndex, cal);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Timestamp getTimestamp(int parameterIndex, Calendar cal) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getTimestamp(parameterIndex, cal);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }
    
    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void registerOutParameter(int parameterIndex, int sqlType, String typeName) throws SQLException {
        validateConnection();

        try {
            _callableStatement.registerOutParameter(parameterIndex, sqlType, typeName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void registerOutParameter(String parameterName, int sqlType) throws SQLException {
        validateConnection();

        try {
            _callableStatement.registerOutParameter(parameterName, sqlType);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void registerOutParameter(String parameterName, int sqlType, int scale) throws SQLException {
        validateConnection();

        try {
            _callableStatement.registerOutParameter(parameterName, sqlType, scale);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void registerOutParameter(String parameterName, int sqlType, String typeName) throws SQLException {
        validateConnection();

        try {
            _callableStatement.registerOutParameter(parameterName, sqlType, typeName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public java.net.URL getURL(int parameterIndex) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getURL(parameterIndex);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setURL(String parameterName, java.net.URL val) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setURL(parameterName, val);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }
    
    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setNull(String parameterName, int sqlType) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setNull(parameterName, sqlType);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setBoolean(String parameterName, boolean x) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setBoolean(parameterName, x);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setByte(String parameterName, byte x) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setByte(parameterName, x);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setShort(String parameterName, short x) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setShort(parameterName, x);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setInt(String parameterName, int x) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setInt(parameterName, x);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setLong(String parameterName, long x) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setLong(parameterName, x);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setFloat(String parameterName, float x) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setFloat(parameterName, x);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setDouble(String parameterName, double x) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setDouble(parameterName, x);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setBigDecimal(String parameterName, BigDecimal x) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setBigDecimal(parameterName, x);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setString(String parameterName, String x) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setString(parameterName, x);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setBytes(String parameterName, byte[] x) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setBytes(parameterName, x);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setDate(String parameterName, Date x) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setDate(parameterName, x);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setTime(String parameterName, Time x) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setTime(parameterName, x);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setTimestamp(String parameterName, Timestamp x) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setTimestamp(parameterName, x);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setAsciiStream(String parameterName, java.io.InputStream x, int length) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setAsciiStream(parameterName, x, length);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setBinaryStream(String parameterName, java.io.InputStream x, int length) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setBinaryStream(parameterName, x, length);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setObject(String parameterName, Object x, int targetSqlType, int scale) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setObject(parameterName, x, targetSqlType, scale);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setObject(String parameterName, Object x, int targetSqlType) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setObject(parameterName, x, targetSqlType);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setObject(String parameterName, Object x) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setObject(parameterName, x);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setCharacterStream(String parameterName, java.io.Reader x, int length) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setCharacterStream(parameterName, x, length);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setDate(String parameterName, Date x, Calendar cal) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setDate(parameterName, x, cal);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setTime(String parameterName, Time x, Calendar cal) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setTime(parameterName, x, cal);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setTimestamp(String parameterName, Timestamp x, Calendar cal) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setTimestamp(parameterName, x, cal);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public void setNull(String parameterName, int sqlType, String typeName) throws SQLException {
        validateConnection();

        try {
            _callableStatement.setNull(parameterName, sqlType, typeName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public String getString(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getString(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public boolean getBoolean(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getBoolean(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return false;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public byte getByte(String parameterName) throws SQLException  {
        validateConnection();

        try {
            return _callableStatement.getByte(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return Byte.MIN_VALUE;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public short getShort(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getShort(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return Short.MIN_VALUE;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public int getInt(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getInt(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return Integer.MIN_VALUE;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public long getLong(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getLong(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return Long.MIN_VALUE;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public float getFloat(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getFloat(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return Float.MIN_VALUE;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public double getDouble(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getDouble(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return Double.MIN_VALUE;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public byte[] getBytes(String parameterName) throws SQLException  {
        validateConnection();

        try {
            return _callableStatement.getBytes(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Date getDate(String parameterName) throws SQLException  {
        validateConnection();

        try {
            return _callableStatement.getDate(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Time getTime(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getTime(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Timestamp getTimestamp(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getTimestamp(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Object getObject(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getObject(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public BigDecimal getBigDecimal(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getBigDecimal(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Object getObject(String parameterName, java.util.Map map) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getObject(parameterName, map);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Ref getRef(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getRef(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Blob getBlob(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getBlob(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Clob getClob(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getClob(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Array getArray(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getArray(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Date getDate(String parameterName, Calendar cal) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getDate(parameterName, cal);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Time getTime(String parameterName, Calendar cal) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getTime(parameterName, cal);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public Timestamp getTimestamp(String parameterName, Calendar cal) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getTimestamp(parameterName, cal);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

    /**
     * Delgates calls to the callable statement; SQLExceptions thrown from the
     * callable statement will cause an event to be fired on the connection
     * pool listeners.
     *
     * @throws SQLException if an error occurs
     */
    public java.net.URL getURL(String parameterName) throws SQLException {
        validateConnection();

        try {
            return _callableStatement.getURL(parameterName);
        } catch (SQLException sqlException) {
            processSQLException(sqlException);
        }
        
        return null;
    }

	@Override
	public void setAsciiStream(int arg0, InputStream arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setAsciiStream(int arg0, InputStream arg1, long arg2)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setBinaryStream(int arg0, InputStream arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setBinaryStream(int arg0, InputStream arg1, long arg2)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setBlob(int arg0, InputStream arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setBlob(int arg0, InputStream arg1, long arg2)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setCharacterStream(int arg0, Reader arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setCharacterStream(int arg0, Reader arg1, long arg2)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setClob(int arg0, Reader arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setClob(int arg0, Reader arg1, long arg2) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setNCharacterStream(int arg0, Reader arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setNCharacterStream(int arg0, Reader arg1, long arg2)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setNClob(int arg0, NClob arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setNClob(int arg0, Reader arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setNClob(int arg0, Reader arg1, long arg2) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setNString(int arg0, String arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setRowId(int arg0, RowId arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setSQLXML(int arg0, SQLXML arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean isClosed() throws SQLException {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isPoolable() throws SQLException {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void setPoolable(boolean arg0) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean isWrapperFor(Class<?> arg0) throws SQLException {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public <T> T unwrap(Class<T> arg0) throws SQLException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Reader getCharacterStream(int arg0) throws SQLException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Reader getCharacterStream(String arg0) throws SQLException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Reader getNCharacterStream(int arg0) throws SQLException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Reader getNCharacterStream(String arg0) throws SQLException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public NClob getNClob(int arg0) throws SQLException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public NClob getNClob(String arg0) throws SQLException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getNString(int arg0) throws SQLException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getNString(String arg0) throws SQLException {
		// TODO Auto-generated method stub
		return null;
	}

//	@Override
//	public Object getObject(int arg0, Map<String, Class<?>> arg1)
//			throws SQLException {
//		// TODO Auto-generated method stub
//		return null;
//	}
//
//	@Override
//	public Object getObject(String arg0, Map<String, Class<?>> arg1)
//			throws SQLException {
//		// TODO Auto-generated method stub
//		return null;
//	}

	@Override
	public RowId getRowId(int arg0) throws SQLException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public RowId getRowId(String arg0) throws SQLException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SQLXML getSQLXML(int arg0) throws SQLException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SQLXML getSQLXML(String arg0) throws SQLException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setAsciiStream(String arg0, InputStream arg1)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setAsciiStream(String arg0, InputStream arg1, long arg2)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setBinaryStream(String arg0, InputStream arg1)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setBinaryStream(String arg0, InputStream arg1, long arg2)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setBlob(String arg0, Blob arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setBlob(String arg0, InputStream arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setBlob(String arg0, InputStream arg1, long arg2)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setCharacterStream(String arg0, Reader arg1)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setCharacterStream(String arg0, Reader arg1, long arg2)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setClob(String arg0, Clob arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setClob(String arg0, Reader arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setClob(String arg0, Reader arg1, long arg2)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setNCharacterStream(String arg0, Reader arg1)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setNCharacterStream(String arg0, Reader arg1, long arg2)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setNClob(String arg0, NClob arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setNClob(String arg0, Reader arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setNClob(String arg0, Reader arg1, long arg2)
			throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setNString(String arg0, String arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setRowId(String arg0, RowId arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setSQLXML(String arg0, SQLXML arg1) throws SQLException {
		// TODO Auto-generated method stub
		
	}
}
